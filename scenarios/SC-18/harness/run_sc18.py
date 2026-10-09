#!/usr/bin/env python3
"""SC-18 log-before-release proxy (unprivileged). Preregistration: prereg/SC18-LOG-PROXY.md (PREREG-SC18-LOGPROXY-v1).

Defensive reference test on one Linux host. A benign client sends requests to a trusted proxy, which forwards them
to a model stub (canned responses), commits a log record {request id, response digest} to a separate log-sink
process (append-only file, fsync per record) and releases the response only after the sink's ack. A watchdog stops
serving (fail closed) when the sink has acked nothing for T seconds. Each hypothesis is repeated --reps times on
fresh processes:

  H1 log-before-release : every response the client received has a committed sink record with the same request id
                          and response digest, committed before the client received it          (sc18_safe)
  H2 sink outage (hang) : the controller SIGSTOPs the sink; no response is released after t_stop + T + TAU_W, and
                          every request sent after that is refused by the watchdog       (sc18_safe, watchdog)
  H3 recovery           : the controller SIGKILLs the sink, the watchdog stops serving, a new sink incarnation is
                          started on the same file; serving resumes within TAU_RESUME and >= 99% of later requests
                          are served; reconciliation holds across both incarnations       (operational extension)
  H4 usefulness         : >= 99% of 200 requests served under normal conditions; latency recorded
  H5 CONTROL fail-open  : the proxy configured to release when the sink fails (NEGATIVE_CONTROL) releases responses
                          during an outage that have NO sink record; reconciliation detects them
                                                                                          (fail_open_outage_breaks)

Receipts go to --out, which must not exist. No root, no accounts: TCP only on 127.0.0.1 (ephemeral ports), the sink
on a Unix socket, all files in a fresh /var/tmp/sc18-run-* directory (on disk, so fsync is real), removed
afterwards. Python 3.9 compatible (system interpreter).
"""
import argparse
import datetime
import hashlib
import http.client
import json
import os
import platform
import re
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC18-LOG-PROXY.md"
PREREG_ID = "PREREG-SC18-LOGPROXY-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5"]
CONTROLS = {"H5"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
T = 1.0                  # s, watchdog: stop serving after T s without any sink ack
ACK_TIMEOUT = 0.3        # s, proxy waits this long for a record ack
HB = 0.1                 # s, proxy pings the sink when its last ack is older than this
THREADS = 4              # client threads
GAP = 0.01               # s, pause between a client thread's requests in timed phases
H1_REQ = 60              # requests (H1), sent back to back by THREADS threads
H4_REQ = 100             # requests (H4)
PRE = 0.5                # s of normal traffic before an outage (H2, H3, H5)
H2_OUT = 2.5             # s of traffic during the hang (> T)
H3_OUT = 1.5             # s of traffic between the crash and the restart (> T)
H3_AFTER = 1.5           # s of traffic after the restart
H5_OUT = 2.0             # s of traffic during the outage, fail-open control
USEFUL_FRAC = 0.99       # H3 (after resume) and H4
MIN_WD_REFUSALS = 10     # H2: at least this many requests refused by the watchdog (non-vacuity)
MIN_WD_REFUSALS_H3 = 5   # H3: same, during the crash outage
CLIENT_TIMEOUT = 5.0     # s
LIFETIME = 30.0          # every child process exits by itself after this
READY_TIMEOUT = 10.0
WALL_LIMIT = 115         # s, whole run
# Tolerances fixed from dry-run calibration (prereg §3.0). Evidence runs refuse unless the prereg says
# CALIBRATION-STATUS: FIXED with the same values.
TAU_W = 0.10             # s (fixed by calibration, prereg §3.0)
TAU_RESUME = 0.25        # s (fixed by calibration, prereg §3.0)


# ---------------------------------------------------------------- plumbing
class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep = hyp, rep
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "negative_control": self.hyp in CONTROLS, "pass": self.passed(),
                "error": self.error, "checks": self.checks, "raw": self.raw}


class Ctx:
    def __init__(self):
        self.work = Path(tempfile.mkdtemp(prefix="sc18-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


def read_tag(p, tag, timeout=READY_TIMEOUT):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, p.pid))
        r, _, _ = select.select([fd], [], [], rem)
        if not r:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before %s from pid %d (rc=%s)" % (tag, p.pid, p.poll()))
        buf += chunk
    line = buf.split(b"\n", 1)[0].decode()
    if not line.startswith(tag + " "):
        raise RuntimeError("unexpected output: %r" % line)
    return json.loads(line[len(tag) + 1:])


def proc_scan(marker):
    out, me = [], os.getpid()
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) == me:
            continue
        try:
            with open("/proc/%s/cmdline" % d, "rb") as fh:
                cmd = fh.read().replace(b"\0", b" ").decode("utf-8", "replace")
            with open("/proc/%s/stat" % d) as fh:
                st = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        state = st[st.rindex(")") + 2:].split()[0]
        if marker in cmd and state not in ("Z", "X"):
            out.append({"pid": int(d), "state": state, "cmd": cmd[:200]})
    return out


class Stack:
    """model stub + log sink + proxy for one repetition"""

    def __init__(self, ctx, tag, fail_open=False):
        self.ctx, self.tag = ctx, tag
        self.d = ctx.work / tag
        self.d.mkdir()
        self.sock, self.log = self.d / "sink.sock", self.d / "sink.log"
        self.commits, self.journal = self.d / "commits.jsonl", self.d / "proxy-journal.jsonl"
        self.procs, self.inc, self.sink = [], 0, None
        self.timeline = []
        self.model = self._spawn("model", ctx.script("model_stub.py", "--lifetime", LIFETIME))
        self.model_port = read_tag(self.model, "READY")["port"]
        self.start_sink()
        args = ["--sink", self.sock, "--model-port", self.model_port, "--T", T, "--ack-timeout", ACK_TIMEOUT,
                "--hb", HB, "--journal", self.journal, "--lifetime", LIFETIME]
        if fail_open:
            args.append("--fail-open")
        self.proxy = self._spawn("proxy", ctx.script("proxy.py", *args))
        self.port = read_tag(self.proxy, "READY")["port"]

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s-%d.stderr" % (self.tag, name, len(self.procs)))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def start_sink(self):
        self.inc += 1
        self.sink = self._spawn("sink", self.ctx.script("log_sink.py", "--sock", self.sock, "--log", self.log,
                                                        "--commits", self.commits, "--inc", self.inc,
                                                        "--lifetime", LIFETIME))
        r = read_tag(self.sink, "READY")
        t = time.monotonic_ns()
        self.timeline.append({"ev": "sink_ready", "inc": self.inc, "t": t, "seq0": r["seq0"]})
        return t

    def signal_sink(self, sig):
        t = time.monotonic_ns()
        self.sink.send_signal(sig)
        if sig == signal.SIGKILL:
            self.sink.wait(timeout=5)
        self.timeline.append({"ev": "sink_signal", "sig": int(sig), "inc": self.inc, "t": t,
                              "t_done": time.monotonic_ns()})
        return t

    def status(self):
        c = http.client.HTTPConnection("127.0.0.1", self.port, timeout=CLIENT_TIMEOUT)
        c.request("GET", "/status")
        s = json.loads(c.getresponse().read())
        c.close()
        return s

    def close(self):
        for p in self.procs:
            if p.poll() is None:
                try:
                    p.kill()
                except OSError:
                    pass
        for p in self.procs:
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            if p.stdout:
                p.stdout.close()


def one_request(port, rid):
    body = json.dumps({"prompt": "benign test prompt %s" % rid}).encode()
    rec = {"rid": rid, "t_send": time.monotonic_ns()}
    try:
        c = http.client.HTTPConnection("127.0.0.1", port, timeout=CLIENT_TIMEOUT)
        c.request("POST", "/v1/complete", body=body, headers={"Content-Type": "application/json",
                                                               "X-Request-Id": rid})
        r = c.getresponse()
        data = r.read()
        c.close()
        rec.update(status=r.status, reason=r.getheader("X-Refuse"), unlogged_hdr=r.getheader("X-Unlogged"),
                   digest=hashlib.sha256(data).hexdigest() if r.status == 200 else None)
    except (OSError, http.client.HTTPException) as e:
        rec.update(status=None, reason="client-error: %s" % e, unlogged_hdr=None, digest=None)
    rec["t_rx"] = time.monotonic_ns()
    rec["lat_s"] = (rec["t_rx"] - rec["t_send"]) / 1e9
    return rec


class Traffic:
    """THREADS client threads; either n requests each back to back, or timed with GAP until stop()"""

    def __init__(self, port, tag, n_each=None):
        self.port, self.tag, self.n_each = port, tag, n_each
        self.recs, self.lock, self.stop_ev = [], threading.Lock(), threading.Event()
        self.ts = [threading.Thread(target=self._run, args=(i,), daemon=True) for i in range(THREADS)]
        for t in self.ts:
            t.start()

    def _run(self, i):
        k = 0
        while not self.stop_ev.is_set() and (self.n_each is None or k < self.n_each):
            r = one_request(self.port, "%s-t%d-%04d" % (self.tag, i, k))
            with self.lock:
                self.recs.append(r)
            k += 1
            if self.n_each is None:
                self.stop_ev.wait(GAP)

    def stop(self):
        if self.n_each is None:
            self.stop_ev.set()
        for t in self.ts:
            t.join(timeout=60 if self.n_each else CLIENT_TIMEOUT + 2)
        return sorted(self.recs, key=lambda r: r["t_send"])


def keep(out, st, client):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.log, st.commits, st.journal):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    with open(str(d / "client.jsonl"), "w") as fh:
        for r in client:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    with open(str(d / "timeline.json"), "w") as fh:
        json.dump(st.timeline, fh, indent=1)


def load_sink(st):
    sink = reconcile.load_jsonl(str(st.log)) if st.log.exists() else []
    commits = reconcile.load_jsonl(str(st.commits)) if st.commits.exists() else []
    return sink, commits


def pct(xs, q):
    if not xs:
        return None
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(q * (len(xs) - 1))))]


def lat_stats(client):
    ls = [c["lat_s"] for c in client if c["status"] == 200]
    return {"n": len(ls), "p50_ms": None if not ls else round(pct(ls, 0.5) * 1e3, 2),
            "p95_ms": None if not ls else round(pct(ls, 0.95) * 1e3, 2),
            "p99_ms": None if not ls else round(pct(ls, 0.99) * 1e3, 2),
            "max_ms": None if not ls else round(max(ls) * 1e3, 2)}


def reasons(rs):
    out = {}
    for r in rs:
        k = "200" if r["status"] == 200 else "%s:%s" % (r["status"], r["reason"])
        out[k] = out.get(k, 0) + 1
    return out


def check_reconcile(R, client, sink, commits, name="H1 rule"):
    rc = reconcile.reconcile(client, sink, commits, T)
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every released response has a committed sink record with matching id and digest, committed before "
            "release, within T, no id released twice (sc18_safe)" % name,
            {"unlogged": 0, "mismatched": 0, "not_before": 0, "stale": 0, "dup": 0},
            {"released": rc["released"], "unlogged": len(rc["unlogged"]), "mismatched": len(rc["mismatched"]),
             "not_before": len(rc["commit_not_before_release"]), "stale": len(rc["stale"]),
             "dup": len(rc["dup_released"])}, rc["ok"])
    return rc


def halt_events(status, after):
    return [e for e in status["events"] if e["ev"] == "halt" and e["t"] >= after]


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        client = Traffic(st.port, st.tag, n_each=H1_REQ // THREADS).stop()
        status = st.status()
    finally:
        st.close()
    sink, commits = load_sink(st)
    keep(out, st, client)
    R.raw.update(status=status, reasons=reasons(client), latency=lat_stats(client), timeline=st.timeline)
    served = sum(1 for c in client if c["status"] == 200)
    R.check("non-vacuity: responses were released", ">= 1", served, served >= 1)
    check_reconcile(R, client, sink, commits)
    mt = reconcile.mutation_selftest(client, sink, commits, T)
    R.check("reconciliation sensitivity: each injected defect in a copy of the stored logs is flagged", True, mt,
            all(mt.values()))


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    try:
        tr = Traffic(st.port, st.tag)
        time.sleep(PRE)
        t_stop = st.signal_sink(signal.SIGSTOP)
        time.sleep(H2_OUT)
        client = tr.stop()
        status = st.status()
    finally:
        st.close()
    sink, commits = load_sink(st)
    keep(out, st, client)
    t_lim = t_stop + int((T + TAU_W) * 1e9)
    after = [c for c in client if c["t_send"] >= t_lim]
    late_rel = [c["rid"] for c in client if c["status"] == 200 and c["t_rx"] > t_lim]
    rel_after_stop = [c["rid"] for c in client if c["status"] == 200 and c["t_send"] > t_stop]
    hs = halt_events(status, t_stop - int(T * 1e9))
    R.raw.update(status=status, t_stop=t_stop, reasons_before=reasons([c for c in client if c["t_send"] < t_stop]),
                 reasons_outage=reasons([c for c in client if c["t_send"] >= t_stop]),
                 released_sent_after_stop=rel_after_stop, timeline=st.timeline,
                 halt_after_stop_s=None if not hs else (hs[0]["t"] - t_stop) / 1e9)
    served_pre = sum(1 for c in client if c["status"] == 200 and c["t_send"] < t_stop)
    R.check("precondition: responses released before the outage", ">= 1", served_pre, served_pre >= 1)
    check_reconcile(R, client, sink, commits)
    R.check("H2: no response released after t_stop + T + TAU_W", 0, late_rel, not late_rel)
    wd = [c for c in after if c["status"] == 503 and c["reason"] == "watchdog"]
    R.check("H2: every request sent after t_stop + T + TAU_W refused by the watchdog (fail closed)",
            {"all_watchdog": True, "n": ">= %d" % MIN_WD_REFUSALS},
            {"n_after": len(after), "n_watchdog": len(wd), "other": reasons([c for c in after if c not in wd])},
            len(wd) == len(after) >= MIN_WD_REFUSALS)
    R.check("H2: proxy watchdog stopped serving within T + TAU_W of t_stop", "<= %.2f s" % (T + TAU_W),
            R.raw["halt_after_stop_s"], hs and hs[0]["t"] <= t_lim and not status["serving"])


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    try:
        tr = Traffic(st.port, st.tag)
        time.sleep(PRE)
        t_kill = st.signal_sink(signal.SIGKILL)
        time.sleep(H3_OUT)
        t_restart = st.start_sink()
        time.sleep(H3_AFTER)
        client = tr.stop()
        status = st.status()
    finally:
        st.close()
    sink, commits = load_sink(st)
    keep(out, st, client)
    t_lim = t_kill + int((T + TAU_W) * 1e9)
    outage = [c for c in client if t_lim <= c["t_send"] and c["t_rx"] < t_restart]
    rel_outage = [c["rid"] for c in client if c["status"] == 200 and t_lim < c["t_rx"] < t_restart]
    post = [c for c in client if c["t_send"] >= t_restart]
    first = min((c for c in post if c["status"] == 200), key=lambda c: c["t_rx"], default=None)
    resume_s = None if first is None else (first["t_rx"] - t_restart) / 1e9
    after_resume = [c for c in post if first is not None and c["t_send"] >= first["t_rx"]]
    frac = (sum(1 for c in after_resume if c["status"] == 200) / len(after_resume)) if after_resume else 0.0
    hs = halt_events(status, t_kill - int(T * 1e9))
    rs = [e for e in status["events"] if e["ev"] == "resume" and e["t"] >= t_restart]
    R.raw.update(status=status, t_kill=t_kill, t_restart=t_restart, resume_s=resume_s, frac_after_resume=frac,
                 reasons_outage=reasons([c for c in client if t_kill <= c["t_send"] < t_restart]),
                 reasons_post=reasons(post), timeline=st.timeline,
                 halt_after_kill_s=None if not hs else (hs[0]["t"] - t_kill) / 1e9,
                 incarnations=sorted({r["inc"] for r in sink}))
    check_reconcile(R, client, sink, commits)
    R.check("H3: no response released between t_kill + T + TAU_W and the restart", 0, rel_outage, not rel_outage)
    wd = [c for c in outage if c["status"] == 503 and c["reason"] == "watchdog"]
    R.check("H3: requests during the outage refused by the watchdog", {"all": True, "n": ">= %d" % MIN_WD_REFUSALS_H3},
            {"n": len(outage), "n_watchdog": len(wd)}, len(wd) == len(outage) >= MIN_WD_REFUSALS_H3)
    R.check("H3: watchdog stopped serving within T + TAU_W of the crash", "<= %.2f s" % (T + TAU_W),
            R.raw["halt_after_kill_s"], bool(hs) and hs[0]["t"] <= t_lim)
    R.check("H3: serving resumed within TAU_RESUME of the restarted sink being ready", "<= %.2f s" % TAU_RESUME,
            resume_s, resume_s is not None and resume_s <= TAU_RESUME and bool(rs))
    R.check("H3: >= %.0f%% of requests sent after resumption served" % (USEFUL_FRAC * 100),
            ">= %.2f" % USEFUL_FRAC, {"frac": round(frac, 4), "n": len(after_resume)},
            frac >= USEFUL_FRAC and len(after_resume) >= 10)
    R.check("H3: both sink incarnations' records are in the one log", [1, 2], R.raw["incarnations"],
            R.raw["incarnations"] == [1, 2])


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    try:
        t0 = time.monotonic()
        client = Traffic(st.port, st.tag, n_each=H4_REQ // THREADS).stop()
        wall = time.monotonic() - t0
        status = st.status()
    finally:
        st.close()
    sink, commits = load_sink(st)
    keep(out, st, client)
    served = sum(1 for c in client if c["status"] == 200)
    R.raw.update(status=status, reasons=reasons(client), latency=lat_stats(client), wall_s=round(wall, 3),
                 throughput_rps=round(len(client) / wall, 1), timeline=st.timeline)
    rc = check_reconcile(R, client, sink, commits)
    R.check("H4: >= %.0f%% of %d requests served and logged" % (USEFUL_FRAC * 100, H4_REQ),
            ">= %d" % int(USEFUL_FRAC * H4_REQ), {"served": served, "sent": len(client), "latency": R.raw["latency"]},
            len(client) == H4_REQ and served >= USEFUL_FRAC * H4_REQ and rc["ok"])


def h5(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h5" % rep, fail_open=True)
    try:
        tr = Traffic(st.port, st.tag)
        time.sleep(PRE)
        t_kill = st.signal_sink(signal.SIGKILL)
        time.sleep(H5_OUT)
        client = tr.stop()
        status = st.status()
    finally:
        st.close()
    sink, commits = load_sink(st)
    keep(out, st, client)
    hs = halt_events(status, t_kill - int(T * 1e9))
    R.raw.update(configuration="NEGATIVE_CONTROL: proxy --fail-open", status=status, t_kill=t_kill,
                 reasons=reasons(client), timeline=st.timeline,
                 halt_after_kill_s=None if not hs else (hs[0]["t"] - t_kill) / 1e9)
    rc = reconcile.reconcile(client, sink, commits, T)
    R.raw["reconcile"] = {"H1 rule": rc}
    un = rc["unlogged"]
    R.check("precondition: proxy runs the fail-open configuration", True, status["fail_open"], status["fail_open"])
    R.check("H5 CONTROL fires: reconciliation finds released responses with no sink record "
            "(fail_open_outage_breaks)", {"unlogged": ">= 1", "H1 rule": "FAILS"},
            {"unlogged": len(un), "H1 rule ok": rc["ok"]}, len(un) >= 1 and not rc["ok"])
    nb = rc["commit_not_before_release"]
    pre = [u for u in un + nb if u["t_rx"] < t_kill]
    R.check("the defective releases (unlogged, or record without a commit before release) all fall after the sink "
            "was killed", 0, len(pre), not pre)
    R.check("no other defect types (mismatched digest, stale, duplicate)", {"mismatched": 0, "stale": 0, "dup": 0},
            {"mismatched": len(rc["mismatched"]), "stale": len(rc["stale"]), "dup": len(rc["dup_released"]),
             "not_before_info": len(nb)},
            not (rc["mismatched"] or rc["stale"] or rc["dup_released"]))
    R.raw["unlogged_window_s"] = None if not un else [round((min(u["t_rx"] for u in un) - t_kill) / 1e9, 4),
                                                      round((max(u["t_rx"] for u in un) - t_kill) / 1e9, 4)]


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-C", str(REPO)] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


def calibration():
    txt = PREREG.read_text() if PREREG.exists() else ""
    st = re.search(r"^CALIBRATION-STATUS: (\w+)\s*$", txt, re.M)
    taus = {k: float(v) for k, v in re.findall(r"^(TAU_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_taus": taus,
            "harness_taus": {"TAU_W": TAU_W, "TAU_RESUME": TAU_RESUME}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    return {
        "prereg_id": PREREG_ID,
        "kind": args.kind,
        "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"),
        "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--untracked-files=all", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "model_sha256": {"ControlStack/Scenarios/SC18Logging.lean": sha(REPO / "ControlStack/Scenarios/SC18Logging.lean")},
        "calibration": calibration(),
        "uname_r": platform.release(),
        "uname_a": " ".join(platform.uname()),
        "python": sys.version,
        "python_executable": sys.executable,
        "nproc": os.cpu_count(),
        "uid": os.getuid(),
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); sink and client stamps on one host",
        "constants": {k: globals()[k] for k in ("T", "ACK_TIMEOUT", "HB", "THREADS", "GAP", "H1_REQ", "H4_REQ", "PRE",
                                                 "H2_OUT", "H3_OUT", "H3_AFTER", "H5_OUT", "USEFUL_FRAC",
                                                 "MIN_WD_REFUSALS", "MIN_WD_REFUSALS_H3", "CLIENT_TIMEOUT",
                                                 "LIFETIME", "WALL_LIMIT", "TAU_W", "TAU_RESUME")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc18-run-")
    if stale:
        problems.append("processes of an earlier sc18 run still alive: %s" % [e["pid"] for e in stale])
    if args.kind == "evidence":
        if m["git_status_harness_and_prereg"]:
            problems.append("evidence run needs committed, unmodified harness and prereg files")
        c = m["calibration"]
        if c["status"] != "FIXED":
            problems.append("prereg calibration status is %s, not FIXED (prereg §3.0)" % c["status"])
        for k, v in c["harness_taus"].items():
            if c["prereg_taus"].get(k) != float(v):
                problems.append("harness %s %s != prereg %s" % (k, v, c["prereg_taus"].get(k)))
    return problems


def summary_md(m, verdicts, results):
    lines = ["# SC-18 log-before-release proxy (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TAU_W = %s s, TAU_RESUME = %s s" % (m["calibration"]["status"], TAU_W, TAU_RESUME),
             "- kernel: `%s`, python `%s`" % (m["uname_r"], m["python"].split()[0]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | kind | reps passed | verdict |", "|---|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %s | %d/%d | %s |" % (h, "NEGATIVE_CONTROL" if h in CONTROLS else "claim",
                                                     v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Key measurements per repetition", "",
              "| hyp | rep | released | unlogged | outcomes | watchdog halt after outage s | resume s | latency p50/p99 ms |",
              "|---|---|---|---|---|---|---|---|"]
    for r in results:
        raw = r["raw"]
        rc = (raw.get("reconcile") or {}).get("H1 rule") or {}
        lat = raw.get("latency") or {}
        oc = raw.get("reasons") or raw.get("reasons_outage") or {}
        lines.append("| %s | %d | %s | %s | %s | %s | %s | %s |" % (
            r["hyp"], r["rep"], rc.get("released", "-"), len(rc.get("unlogged", [])) if rc else "-",
            json.dumps(oc), raw.get("halt_after_stop_s", raw.get("halt_after_kill_s", "-")),
            raw.get("resume_s", "-"), "%s/%s" % (lat.get("p50_ms", "-"), lat.get("p99_ms", "-")) if lat else "-"))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"], default=str)[:400]))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-18 log-before-release proxy check (unprivileged).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    args = ap.parse_args()
    if os.geteuid() == 0:
        sys.exit("refusing to run as root: this harness is unprivileged by design")
    hyps = [h for h in args.only.split(",") if h]
    if any(h not in HYPS for h in hyps):
        sys.exit("unknown hypothesis in --only")
    if args.kind == "evidence" and (hyps != HYPS or args.reps != 5):
        sys.exit("evidence runs use all hypotheses and --reps 5 (prereg §4)")
    out = Path(args.out)
    if out.exists():
        sys.exit("refusing to overwrite existing --out %s" % out)
    if not out.parent.is_dir():
        sys.exit("parent of --out does not exist: %s" % out.parent)
    m = meta(args)
    problems = preflight(args, m)
    if args.kind == "evidence" and problems:
        sys.exit("refusing evidence run: " + "; ".join(problems))
    out.mkdir()
    (out / "logs").mkdir()
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, infra, aborted, ctx, residue = [], None, None, None, None
    if problems:
        infra = problems
    else:
        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            ctx = Ctx()
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    R = Rec(h, rep)
                    t = time.monotonic()
                    try:
                        H[h](ctx, out, rep, R)
                    except WallLimit:
                        R.error = traceback.format_exc()
                        results.append(R.as_dict())
                        raise
                    except Exception:
                        R.error = traceback.format_exc()
                    R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                    left = proc_scan(str(ctx.work))
                    R.raw["after"] = {"left_procs": left, "loadavg": os.getloadavg()}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL", R.raw["elapsed_s"]),
                          flush=True)
                    if left:
                        aborted = "residue after %s rep %d: %s" % (h, rep, left)
                        raise RuntimeError(aborted)
        except BaseException:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                residue = proc_scan(str(ctx.work))
                for e in residue:
                    try:
                        os.kill(e["pid"], signal.SIGKILL)
                    except OSError:
                        pass
                shutil.rmtree(str(ctx.work), ignore_errors=True)
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    cleanup = {"residue_killed": residue, "workdir_removed": ctx is None or not ctx.work.exists()}
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        complete = len(rs) == args.reps
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok, "negative_control": h in CONTROLS,
                  "verdict": "NOT-RUN" if infra else "PASS" if complete and n_ok == args.reps else "FAIL"}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": not residue and cleanup["workdir_removed"], "per_hypothesis": per,
                "calibration": m["calibration"]}
    verdicts["overall"] = ("INFRA-ERROR" if infra else
                           "PASS" if not aborted and verdicts["cleanup_ok"] and all(
                               v["verdict"] == "PASS" for v in per.values()) else "FAIL")
    dump = lambda name, obj: (out / name).write_text(json.dumps(obj, indent=1, sort_keys=True, default=str) + "\n")
    dump("meta.json", m)
    dump("verdicts.json", verdicts)
    dump("cleanup.json", cleanup)
    with open(str(out / "results.jsonl"), "w") as fh:
        for r in results:
            fh.write(json.dumps(r, sort_keys=True, default=str) + "\n")
    (out / "summary.md").write_text(summary_md(m, verdicts, results))
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra},
                     indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
