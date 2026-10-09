#!/usr/bin/env python3
"""DC-1 single-host rehearsal: fencing sink vs. HALT delivery (unprivileged). Preregistration:
prereg/DC1-REHEARSAL-SINGLEHOST.md (PREREG-DC1R-SINGLEHOST-v1).

Defensive reference test on one Linux host, a stand-in for DC-1 (prereg/DC1-DISTRIBUTED-HALT-DRAFT.md). N = 8 benign
worker processes emit small JSON effects at rate <= rho to one sink process over a Unix socket. The controller (this
runner) issues HALT at t0: it marks t0 at the sink, sends HALT to worker i after an injected delay delta_i <= Delta
(one designated worker, "partitioned", never receives HALT in H2-H4), and bumps the sink's epoch at t0 + eps. The
sink stamps every landing with its own CLOCK_MONOTONIC and, with fencing on, rejects effects whose epoch is below
the current one. Each hypothesis is repeated --reps times on fresh processes:

  H1 unfenced, all delivered  : accepted landings after t0 <= n*rho*(L_hat + Delta_hat) + TAU_A     (landed_after_le)
  H2 fenced, one partitioned  : 0 accepted landings at or after t0 + eps_hat                         (fenced_after_eps,
                                and <= n*rho*(L_hat + eps_hat) + TAU_A after t0                       fenced_window,
                                                                                                      partition_fenced)
  H3 CONTROL unfenced + partitioned : the partitioned worker's accepted landings after t0 keep growing
                                (strictly increasing over 4 checkpoints, slope >= 0.8 rho) and exceed the
                                bounded-delivery bound                                                (partition_unbounded)
  H4 CONTROL fenced, the partitioned worker handed the new epoch before t0 : >= 1 of its landings accepted after
                                t0 + eps_hat, none from any other worker                              (token_leak)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/dc1r-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
"""
import argparse
import datetime
import gzip
import hashlib
import json
import os
import platform
import re
import select
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import analyse  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "DC1-REHEARSAL-SINGLEHOST.md"
PREREG_ID = "PREREG-DC1R-SINGLEHOST-v1"
HYPS = ["H1", "H2", "H3", "H4"]
CONTROLS = {"H3", "H4"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
N = 8                       # workers
RHO = 50.0                  # effects per second per worker (upper bound; spacing >= 1/RHO)
E0 = 1                      # epoch held by every worker; the fence bumps to E0 + 1
DELTA = 0.20                # s, largest injected HALT delivery delay; delta_i = DELTA * i / (N - 1)
EPS = 0.05                  # s, controller sleeps EPS after t0 before sending BUMP
WARMUP = 0.5                # s of emission before t0
OBS = {"H1": 1.0, "H2": 2.0, "H3": 3.0, "H4": 1.5}   # s observed after t0
CHECKPOINTS = [0.75, 1.5, 2.25, 3.0]                 # s after t0, H3 growth series
PARTITIONED = N - 1         # designated worker that never receives HALT (H2, H3, H4)
LEAK_BEFORE = 0.2           # s before t0, H4: the partitioned worker is handed epoch E0 + 1
GROW_FRAC = 0.8             # H3 slope >= GROW_FRAC * RHO per s; H2 non-vacuity >= GROW_FRAC * RHO * (OBS - eps)
L_SANITY = 0.05             # s, measured in-flight latency must stay below this (premise sanity)
DELTA_SANITY = DELTA + 0.05  # s, measured max delivery delay must stay below this
EPS_SANITY = EPS + 0.05     # s, measured eps must stay below this
GAP_SLACK = 1e-5            # s, rate premise: every initiation gap >= 1/RHO - GAP_SLACK
LIFETIME = 30.0             # every child process exits by itself after this
READY_TIMEOUT = 10.0
WALL_LIMIT = 115            # s, whole run
# Tolerance fixed from dry-run calibration (prereg §3.0). Evidence runs refuse unless the prereg says
# CALIBRATION-STATUS: FIXED with the same value.
TAU_A = 8                   # effects (fixed by calibration, prereg §3.0: the n x (+1) discretisation floor)


# ---------------------------------------------------------------- process plumbing
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
        self.work = Path(tempfile.mkdtemp(prefix="dc1r-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable
        self.procs = []

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


class Reader:
    """line reader over a child's stdout pipe (non-blocking, keeps leftovers)"""

    def __init__(self, p):
        self.p, self.buf, self.lines = p, b"", []

    def pump(self, timeout):
        r, _, _ = select.select([self.p.stdout.fileno()], [], [], timeout)
        if not r:
            return False
        chunk = os.read(self.p.stdout.fileno(), 65536)
        if not chunk:
            return None
        self.buf += chunk
        while b"\n" in self.buf:
            line, self.buf = self.buf.split(b"\n", 1)
            self.lines.append(line.decode())
        return True

    def wait_tag(self, tag, timeout=READY_TIMEOUT):
        t_end = time.monotonic() + timeout
        while True:
            for ln in self.lines:
                if ln.startswith(tag + " "):
                    return json.loads(ln[len(tag) + 1:])
            rem = t_end - time.monotonic()
            if rem <= 0:
                raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, self.p.pid))
            if self.pump(rem) is None:
                raise RuntimeError("EOF before %s from pid %d (rc=%s)" % (tag, self.p.pid, self.p.poll()))

    def drain(self, timeout=2.0):
        t_end = time.monotonic() + timeout
        while time.monotonic() < t_end:
            if self.pump(max(0.0, t_end - time.monotonic())) is None:
                break
        return self.tags()

    def tags(self):
        out = {}
        for ln in self.lines:
            tag, _, rest = ln.partition(" ")
            try:
                out.setdefault(tag, []).append(json.loads(rest))
            except ValueError:
                out.setdefault("unparsed", []).append(ln)
        return out


def kill_all(procs):
    for p in procs:
        if p.poll() is None:
            try:
                p.kill()
            except OSError:
                pass
    for p in procs:
        try:
            p.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass


def proc_scan(marker):
    """independent /proc scan: live processes whose command line contains marker (our unique work dir)"""
    out = []
    me = os.getpid()
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


def run_condition(ctx, tag, fence, partitioned, leaked, obs):
    """One repetition of one condition. Returns everything the analysis needs; cleans up its processes."""
    d = ctx.work / tag
    d.mkdir()
    eff, ctl_path, log = d / "eff.sock", d / "ctl.sock", d / "sink.log"
    procs, readers, ctl = [], {}, None
    timeline = []
    try:
        with open(str(ctx.logs / (tag + "-sink.stderr")), "wb") as se:
            sink = subprocess.Popen(ctx.script("sink.py", "--effects", eff, "--ctl", ctl_path, "--fence",
                                               "on" if fence else "off", "--epoch", E0, "--log", log,
                                               "--lifetime", LIFETIME),
                                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        procs.append(sink)
        sr = Reader(sink)
        sr.wait_tag("READY")
        ctl = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        ctl.connect(str(ctl_path))
        ctl.settimeout(5.0)
        cf = ctl.makefile("rwb", buffering=0)

        def ctl_cmd(cmd):
            cf.write((cmd + "\n").encode())
            return json.loads(cf.readline())

        workers = []
        for i in range(N):
            with open(str(ctx.logs / ("%s-w%d.stderr" % (tag, i))), "wb") as we:
                p = subprocess.Popen(ctx.script("worker.py", "--id", i, "--sink", eff, "--rate", RHO, "--epoch", E0,
                                                "--lifetime", LIFETIME),
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=we, close_fds=True,
                                     bufsize=0)
            procs.append(p)
            workers.append(p)
            readers[i] = Reader(p)
        for i in range(N):
            readers[i].wait_tag("READY")
        time.sleep(WARMUP - (LEAK_BEFORE if leaked is not None else 0.0))
        if leaked is not None:
            workers[leaked].stdin.write(("EPOCH %d\n" % (E0 + 1)).encode())
            timeline.append({"ev": "leak", "w": leaked, "t": time.monotonic_ns()})
            time.sleep(LEAK_BEFORE)
        mark = ctl_cmd("MARK")
        t0 = mark["t"]
        timeline.append({"ev": "mark", "t": t0})
        plan = [(t0 + int(DELTA * i / (N - 1) * 1e9), "halt", i) for i in range(N) if i != partitioned]
        plan.append((t0 + int(EPS * 1e9), "bump", None))
        plan.sort(key=lambda x: (x[0], x[1] != "halt"))
        for due, what, i in plan:
            wait = (due - time.monotonic_ns()) / 1e9
            if wait > 0:
                time.sleep(wait)
            if what == "halt":
                workers[i].stdin.write(b"HALT\n")
                timeline.append({"ev": "halt_sent", "w": i, "due": due, "t": time.monotonic_ns()})
            else:
                r = ctl_cmd("BUMP %d" % (E0 + 1))
                timeline.append({"ev": "bump", "due": due, "t_sink": r["t"], "t": time.monotonic_ns()})
        rem = (t0 + int(obs * 1e9) - time.monotonic_ns()) / 1e9
        if rem > 0:
            time.sleep(rem)
        t_kill = time.monotonic_ns()
        kill_all(workers)
        timeline.append({"ev": "workers_killed", "t": t_kill, "t_done": time.monotonic_ns()})
        stop = ctl_cmd("STOP")
        timeline.append({"ev": "stop", "t_sink": stop["t"], "counts": stop["counts"]})
        sink.wait(timeout=5)
        reports = {}
        for i in range(N):
            tg = readers[i].drain(0.5)
            reports[i] = {"HALTED": (tg.get("HALTED") or [None])[0], "EPOCHSET": (tg.get("EPOCHSET") or [None])[0],
                          "READY": (tg.get("READY") or [None])[0]}
        return {"log": log, "reports": reports, "timeline": timeline, "sink_rc": sink.returncode}
    finally:
        if ctl is not None:
            ctl.close()
        kill_all(procs)
        for p in procs:
            for f in (p.stdin, p.stdout):
                if f:
                    try:
                        f.close()
                    except OSError:
                        pass


def keep_log(ctx, out, tag, res):
    with open(str(res["log"]), "rb") as src, gzip.open(str(out / "logs" / (tag + "-sink.log.gz")), "wb") as dst:
        shutil.copyfileobj(src, dst)
    with open(str(out / "logs" / (tag + "-workers.json")), "w") as fh:
        json.dump({"reports": res["reports"], "timeline": res["timeline"]}, fh, indent=1, sort_keys=True)


def common_checks(R, m, delivered, undelivered):
    gaps = {w: g for w, g in m["min_gap_s"].items() if g is not None}
    bad_gaps = {w: g for w, g in gaps.items() if g < 1.0 / RHO - GAP_SLACK}
    R.check("premise Rate: every worker's initiation spacing >= 1/rho", ">= %.4f s" % (1.0 / RHO),
            {"min": min(gaps.values()) if gaps else None, "violations": bad_gaps}, not bad_gaps and gaps)
    R.check("premise Latency (sanity): L_hat <= %.3f s" % L_SANITY, "<= %.3f" % L_SANITY, round(m["L_hat_s"], 6),
            m["L_hat_s"] <= L_SANITY)
    R.check("stream integrity: no sequence gaps, no malformed lines", {"seq_gaps": {}, "bad": 0},
            {"seq_gaps": m["seq_gaps"], "bad": m["n_bad"]}, not m["seq_gaps"] and m["n_bad"] == 0)
    R.check("sink decisions equal the registered acceptance rule", 0, m["rule_mismatches"], m["rule_mismatches"] == 0)
    got = sorted(int(w) for w in m["delta_hat_s"])
    R.check("HALT received by exactly the delivered workers", {"delivered": delivered, "undelivered": undelivered},
            {"delivered": got, "undelivered": m["undelivered"]},
            got == delivered and m["undelivered"] == undelivered)
    R.check("premise HaltAbsorbs: no effect initiated after a worker's HALT receipt", [], m["absorb_violations"],
            not m["absorb_violations"])


def h1(ctx, out, rep, R):
    tag = "r%d-h1" % rep
    res = run_condition(ctx, tag, fence=False, partitioned=None, leaked=None, obs=OBS["H1"])
    keep_log(ctx, out, tag, res)
    ef, ct, bd = analyse.load_log(str(res["log"]))
    p = {"n": N, "rho": RHO, "e0": E0, "fence": False}
    m = analyse.measure(ef, ct, bd, res["reports"], p)
    R.raw.update(measure=m, timeline=res["timeline"])
    common_checks(R, m, list(range(N)), [])
    R.check("premise Delivered (sanity): Delta_hat <= %.2f s" % DELTA_SANITY, "<= %.2f" % DELTA_SANITY,
            m["Delta_hat_s"], m["Delta_hat_s"] is not None and m["Delta_hat_s"] <= DELTA_SANITY)
    R.check("non-vacuity: some effects land after t0", ">= 1", m["A_t0"], m["A_t0"] >= 1)
    R.check("H1: accepted landings after t0 <= n*rho*(L_hat+Delta_hat) + TAU_A (landed_after_le)",
            "<= %.2f" % (m["B_unfenced"] + TAU_A),
            {"A_t0": m["A_t0"], "B_unfenced": round(m["B_unfenced"], 2), "B_per_node_sum": round(m["B_unfenced_sum"], 2),
             "excess_over_B": round(m["A_t0"] - m["B_unfenced"], 2)},
            analyse.rule_h1(m, TAU_A))
    mt = analyse.mutation_selftest(ef, ct, bd, res["reports"], p, TAU_A, "h1")
    R.check("analysis sensitivity: the H1 rule fails on a mutated copy of this log", True, mt, all(mt.values()))


def h2(ctx, out, rep, R):
    tag = "r%d-h2" % rep
    res = run_condition(ctx, tag, fence=True, partitioned=PARTITIONED, leaked=None, obs=OBS["H2"])
    keep_log(ctx, out, tag, res)
    ef, ct, bd = analyse.load_log(str(res["log"]))
    p = {"n": N, "rho": RHO, "e0": E0, "fence": True}
    m = analyse.measure(ef, ct, bd, res["reports"], p)
    R.raw.update(measure=m, timeline=res["timeline"])
    common_checks(R, m, [i for i in range(N) if i != PARTITIONED], [PARTITIONED])
    R.check("eps sanity: eps_hat <= %.2f s" % EPS_SANITY, "<= %.2f" % EPS_SANITY, m["eps_hat_s"],
            m["eps_hat_s"] <= EPS_SANITY)
    need = GROW_FRAC * RHO * (OBS["H2"] - m["eps_hat_s"])
    rej = m["R_tF_by_worker"].get(str(PARTITIONED), 0)
    R.check("non-vacuity: the partitioned worker kept emitting after the fence (rejected landings)",
            ">= %.1f" % need, rej, rej >= need)
    R.check("H2: zero accepted landings at or after t0 + eps_hat (fenced_after_eps, partition_fenced)", 0,
            {"A_tF": m["A_tF"], "by_worker": m["A_tF_by_worker"]}, analyse.rule_h2(m))
    R.check("H2 window: accepted landings after t0 <= n*rho*(L_hat+eps_hat) + TAU_A (fenced_window)",
            "<= %.2f" % (m["B_fenced"] + TAU_A), {"A_t0": m["A_t0"], "B_fenced": round(m["B_fenced"], 2)},
            analyse.rule_h2_window(m, TAU_A))
    mt = analyse.mutation_selftest(ef, ct, bd, res["reports"], p, TAU_A, "h2")
    R.check("analysis sensitivity: the H2 rule fails on a mutated copy of this log", True, mt, all(mt.values()))


def h3(ctx, out, rep, R):
    tag = "r%d-h3" % rep
    res = run_condition(ctx, tag, fence=False, partitioned=PARTITIONED, leaked=None, obs=OBS["H3"])
    keep_log(ctx, out, tag, res)
    ef, ct, bd = analyse.load_log(str(res["log"]))
    p = {"n": N, "rho": RHO, "e0": E0, "fence": False}
    m = analyse.measure(ef, ct, bd, res["reports"], p, partitioned=[PARTITIONED], checkpoints=CHECKPOINTS)
    R.raw.update(measure=m, timeline=res["timeline"])
    common_checks(R, m, [i for i in range(N) if i != PARTITIONED], [PARTITIONED])
    Bt = m["B_unfenced"] + TAU_A
    f = analyse.rule_h3(m, PARTITIONED, RHO, GROW_FRAC, Bt)
    R.raw["control"] = f
    R.check("H3 CONTROL fires: partitioned worker's accepted landings after t0 grow without bound "
            "(partition_unbounded)",
            {"increasing": True, "slope_per_s": ">= %.1f" % (GROW_FRAC * RHO), "A_t0": "> %.2f" % Bt},
            {"series": f["series"], "slope_per_s": round(f["slope_per_s"], 2), "A_t0": m["A_t0"]}, f["fires"])
    mt = analyse.mutation_selftest(ef, ct, bd, res["reports"], p, TAU_A, "h3", w=PARTITIONED,
                                   checkpoints=CHECKPOINTS, frac=GROW_FRAC, B_plus_tau=Bt)
    R.check("analysis sensitivity: the H3 detector does not fire on a mutated copy of this log", True, mt,
            all(mt.values()))


def h4(ctx, out, rep, R):
    tag = "r%d-h4" % rep
    res = run_condition(ctx, tag, fence=True, partitioned=PARTITIONED, leaked=PARTITIONED, obs=OBS["H4"])
    keep_log(ctx, out, tag, res)
    ef, ct, bd = analyse.load_log(str(res["log"]))
    p = {"n": N, "rho": RHO, "e0": E0, "fence": True}
    m = analyse.measure(ef, ct, bd, res["reports"], p)
    R.raw.update(measure=m, timeline=res["timeline"])
    common_checks(R, m, [i for i in range(N) if i != PARTITIONED], [PARTITIONED])
    es = res["reports"][PARTITIONED]["EPOCHSET"]
    R.check("leak applied before t0 (worker reports holding epoch %d)" % (E0 + 1), True,
            es, es is not None and es["epoch"] == E0 + 1 and es["t"] < m["t0_ns"])
    f = analyse.rule_h4(m, PARTITIONED)
    R.raw["control"] = f
    R.check("H4 CONTROL fires: the worker holding the new epoch gets landings accepted after t0 + eps_hat, "
            "no other worker does (token_leak)", {"leaked": ">= 1", "others": {}},
            {"leaked": f["leaked_accepted_after_tF"], "others": f["others_accepted_after_tF"]}, f["fires"])
    R.check("every accepted landing after the fence carries the new epoch", [E0 + 1], m["epochs_accepted_after_tF"],
            m["epochs_accepted_after_tF"] == [E0 + 1])
    mt = analyse.mutation_selftest(ef, ct, bd, res["reports"], p, TAU_A, "h4", w=PARTITIONED)
    R.check("analysis sensitivity: the H4 detector does not fire on a mutated copy of this log", True, mt,
            all(mt.values()))


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4}


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
    """CALIBRATION-STATUS and TAU_* lines of the prereg (§3.0)"""
    txt = PREREG.read_text() if PREREG.exists() else ""
    st = re.search(r"^CALIBRATION-STATUS: (\w+)\s*$", txt, re.M)
    taus = {k: float(v) for k, v in re.findall(r"^(TAU_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_taus": taus, "harness_taus": {"TAU_A": TAU_A}}


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
        "model_sha256": {"ControlStack/Families/F3/DistributedHalt.lean":
                         sha(REPO / "ControlStack/Families/F3/DistributedHalt.lean")},
        "calibration": calibration(),
        "uname_r": platform.release(),
        "uname_a": " ".join(platform.uname()),
        "python": sys.version,
        "python_executable": sys.executable,
        "nproc": os.cpu_count(),
        "uid": os.getuid(),
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC), stamped by the sink; one host",
        "constants": {k: globals()[k] for k in ("N", "RHO", "E0", "DELTA", "EPS", "WARMUP", "OBS", "CHECKPOINTS",
                                                 "PARTITIONED", "LEAK_BEFORE", "GROW_FRAC", "L_SANITY",
                                                 "DELTA_SANITY", "EPS_SANITY", "GAP_SLACK", "LIFETIME", "TAU_A",
                                                 "WALL_LIMIT")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/dc1r-run-")
    if stale:
        problems.append("processes of an earlier dc1r run still alive: %s" % [e["pid"] for e in stale])
    if args.kind == "evidence":
        if m["git_status_harness_and_prereg"]:
            problems.append("evidence run needs committed, unmodified harness and prereg files")
        c = m["calibration"]
        if c["status"] != "FIXED":
            problems.append("prereg calibration status is %s, not FIXED (prereg §3.0)" % c["status"])
        if c["prereg_taus"].get("TAU_A") != float(TAU_A):
            problems.append("harness TAU_A %s != prereg TAU_A %s" % (TAU_A, c["prereg_taus"].get("TAU_A")))
    return problems


def summary_md(m, verdicts, results):
    lines = ["# DC-1 single-host rehearsal (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TAU_A = %s" % (m["calibration"]["status"], TAU_A),
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
              "| hyp | rep | A_t0 | A_tF | B (n·ρ·(L̂+Δ̂) or n·ρ·(L̂+ε̂)) | L̂ ms | Δ̂ ms | ε̂ ms | quiescence s |",
              "|---|---|---|---|---|---|---|---|---|"]
    for r in results:
        mm = r["raw"].get("measure")
        if not mm:
            continue
        B = mm.get("B_unfenced") if r["hyp"] in ("H1", "H3") else mm.get("B_fenced")
        f = lambda x, k=1000.0: "-" if x is None else "%.1f" % (x * k)
        lines.append("| %s | %d | %d | %s | %s | %s | %s | %s | %s |" % (
            r["hyp"], r["rep"], mm["A_t0"], mm["A_tF"], "-" if B is None else "%.1f" % B, f(mm["L_hat_s"]),
            f(mm["Delta_hat_s"]), f(mm["eps_hat_s"]), f(mm["quiescence_after_t0_s"], 1.0)))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"], default=str)))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="DC-1 single-host fencing-sink rehearsal (unprivileged).")
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
