#!/usr/bin/env python3
"""SC-27 hash-chained evidence log with an independent anchor (unprivileged). Preregistration:
prereg/SC27-ANCHOR-CHAIN.md (PREREG-SC27-ANCHOR-v1).

Defensive reference test on one Linux host. A writer process appends evidence entries to a hash-chained log whose
storage it controls. An independent witness process periodically recomputes each log's head from storage and records
it in its OWN log (refusing, as a fork, any state that does not extend its previous anchor). A verifier accepts a
manifest only if its recomputed head equals a witness-anchored head. This runner plays the writer-side adversary in a
benign, scripted way: it rewrites the writer's storage. Each hypothesis is repeated --reps times on fresh processes:

  H1 every post-anchor tamper kind is rejected: modify an old entry, reorder, truncate, append an unanchored suffix,
     full rewrite with recomputed hashes          (sc27_safe, tamper_after_anchor_detected, unanchored_suffix_breaks
                                                    deployed half)
  H2 honest manifests are accepted, within the anchor period P + TAU_A of the last append       (honest_accept)
  H3 the honest limit: a rewrite BEFORE the first anchor of the entries IS accepted; after it, rejected; the window
     (append -> first anchor) is <= P + TAU_W                                        (rewrite_before_anchor_window)
  H4 NEGATIVE_CONTROL: a verifier checking the writer's current storage head, and one accepting heads the writer
     published itself, accept a fabricated log; detected against the witness's own log
                                                                 (no_anchor_rollback_breaks, self_signed_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/sc27-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
"""
import argparse
import datetime
import hashlib
import json
import math
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
import chain  # noqa: E402
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC27-ANCHOR-CHAIN.md"
PREREG_ID = "PREREG-SC27-ANCHOR-v1"
HYPS = ["H1", "H2", "H3", "H4"]
CONTROLS = {"H4"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
P = 0.25                    # s, witness anchor period (H2, H3)
H1_ENTRIES = 20
H2_ROUNDS, H2_BATCH = 8, 3
H3_TRIALS = 10
H3_DELAYS = [round(j * 1.5 * P / (H3_TRIALS - 1), 4) for j in range(H3_TRIALS)]   # 0 .. 1.5 P
POLL = 0.01
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Tolerances fixed from dry-run calibration (prereg §3.0).
TAU_A = 0.05                # s (calibrated)
TAU_W = 0.05                # s (calibrated)


def entry(log, i, fake=False):
    return {"log": log, "k": i, "evidence": ("FABRICATED result %d: all checks passed" if fake else
                                             "test run %d: 42 passed, 0 failed") % i}


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
        self.work = Path(tempfile.mkdtemp(prefix="sc27-run-", dir="/var/tmp"))
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


def ancestors():
    out, pid = set(), os.getpid()
    while pid > 1:
        out.add(pid)
        try:
            with open("/proc/%d/status" % pid) as fh:
                pid = int([l for l in fh if l.startswith("PPid:")][0].split()[1])
        except (OSError, IndexError, ValueError):
            break
    return out


def proc_scan(marker):
    """live processes (not this runner or its ancestors) with a command-line ARGUMENT that starts with marker"""
    out, skip = [], ancestors()
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) in skip:
            continue
        try:
            with open("/proc/%s/cmdline" % d, "rb") as fh:
                args = [x.decode("utf-8", "replace") for x in fh.read().split(b"\0") if x]
            with open("/proc/%s/stat" % d) as fh:
                st = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        state = st[st.rindex(")") + 2:].split()[0]
        if any(x.startswith(marker) for x in args) and state not in ("Z", "X"):
            out.append({"pid": int(d), "state": state, "cmd": " ".join(args)[:200]})
    return out


def rpc(path, obj, timeout=10.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(str(path))
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


class Stack:
    """writer + independent witness + verifier"""

    def __init__(self, ctx, tag, period, verifier_flags=()):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.store, wdir = d / "store", d / "witness"
        wdir.mkdir(mode=0o700)
        self.wlog, self.vlog = wdir / "witness.jsonl", d / "verifier.jsonl"
        lib = str(HERE)
        read_tag(self._spawn("writer", ctx.script("writer.py", "--lib", lib, "--store", self.store, "--sock",
                                                  d / "writer.sock", "--lifetime", LIFETIME)), "READY")
        read_tag(self._spawn("witness", ctx.script("witness.py", "--lib", lib, "--store", self.store, "--sock",
                                                   d / "witness.sock", "--log", self.wlog, "--period", period,
                                                   "--lifetime", LIFETIME)), "READY")
        v = self._spawn("verifier", ctx.script("verifier.py", "--lib", lib, "--witness-log", self.wlog, "--store",
                                               self.store, "--sock", d / "verifier.sock", "--log", self.vlog,
                                               "--lifetime", LIFETIME, *verifier_flags))
        self.config = read_tag(v, "READY")["config"]
        self.config["period"] = period

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def path(self, log):
        return str(self.store / ("log-%s.jsonl" % log))

    def append(self, log, e):
        return rpc(self.d / "writer.sock", {"op": "append", "log": log, "entry": e})

    def publish(self, log, head):
        return rpc(self.d / "writer.sock", {"op": "publish_head", "log": log, "head": head})

    def anchor_now(self, log):
        return rpc(self.d / "witness.sock", {"op": "anchor_now", "log": log})["rec"]

    def verify(self, log, entries):
        return rpc(self.d / "verifier.sock", {"op": "verify", "log": log, "entries": entries})

    def storage(self, log):
        return chain.read_entries(self.path(log))

    def rewrite(self, log, entries):
        """writer-side adversary: replace the storage with entries and a consistently recomputed chain"""
        chain.write_storage(self.path(log), entries)

    def witness(self):
        return reconcile.witness_records(str(self.wlog))

    def verdicts(self):
        return reconcile.load_jsonl(str(self.vlog))

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


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    shutil.copytree(str(st.store), str(d / "store"))
    shutil.copy2(str(st.wlog), str(d / "witness.jsonl")) if st.wlog.exists() else None
    shutil.copy2(str(st.vlog), str(d / "verifier.jsonl")) if st.vlog.exists() else None
    if extra is not None:
        with open(str(d / "client.json"), "w") as fh:
            json.dump(extra, fh, indent=1, default=str)


def check_reconcile(R, rc, name="reconciliation"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every accepted manifest's head was anchored by the independent witness for that log (sc27_safe)"
            % name, {"accepted_unanchored": []}, {"accepted": rc["accepted"], "rejected": rc["rejected"],
                                                  "accepted_unanchored": rc["accepted_unanchored"]}, rc["ok"])


TAMPERS = {
    "modify an old entry": lambda es: [dict(e, evidence="test run %d: 41 passed, 1 failed" % e["k"]) if e["k"] == 3
                                       else e for e in es],
    "reorder two entries": lambda es: es[:5] + [es[6], es[5]] + es[7:],
    "truncate the last 3": lambda es: es[:-3],
    "append an unanchored suffix": lambda es: es + [entry("main", len(es)), entry("main", len(es) + 1)],
    "full rewrite with recomputed hashes": lambda es: [entry("main", e["k"], fake=True) for e in es],
}


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep, 0)
    res = {}
    try:
        for i in range(H1_ENTRIES):
            st.append("main", entry("main", i))
        a0 = st.anchor_now("main")
        orig = st.storage("main")
        res["original"] = st.verify("main", orig)
        for kind, f in TAMPERS.items():
            st.rewrite("main", f(orig))
            v = st.verify("main", st.storage("main"))
            w = st.anchor_now("main") if kind != "append an unanchored suffix" else None
            res[kind] = {"verify": v, "witness_on_tampered_storage": w}
            st.rewrite("main", orig)
            res[kind]["witness_after_restore"] = st.anchor_now("main")["kind"]
        res["original again"] = st.verify("main", orig)
    finally:
        st.close()
    wit, ver = st.witness(), st.verdicts()
    keep(out, st, res)
    rej = {k: res[k]["verify"]["accepted"] for k in TAMPERS}
    R.raw.update(first_anchor=a0, results={k: {"accepted": res[k]["verify"]["accepted"],
                                              "witness": (res[k]["witness_on_tampered_storage"] or {}).get("kind")}
                                          for k in TAMPERS})
    R.check("non-vacuity: the anchored original manifest is accepted (honest_accept)", [True, True],
            [res["original"]["accepted"], res["original again"]["accepted"]],
            res["original"]["accepted"] and res["original again"]["accepted"] and a0["kind"] == "anchor")
    R.check("H1: every post-anchor tamper kind is rejected (tamper_after_anchor_detected, unanchored_suffix_breaks "
            "deployed half, sc27_safe)", {k: False for k in TAMPERS}, rej, not any(rej.values()))
    forks = {k: (res[k]["witness_on_tampered_storage"] or {}).get("kind") for k in TAMPERS
             if k != "append an unanchored suffix"}
    R.check("the witness refuses to anchor tampered storage (fork alarm; an extension beyond the model)",
            {k: "fork" for k in forks}, forks, all(v == "fork" for v in forks.values()))
    anchored = [r for r in wit if r["kind"] == "anchor"]
    R.check("the witness anchored only the honest log", 1, len(anchored),
            len(anchored) == 1 and anchored[0]["head"] == chain.head_of(orig))
    check_reconcile(R, reconcile.reconcile(ver, wit))
    mt = reconcile.mutation_selftest(ver, wit)
    R.check("reconciliation sensitivity: each injected defect is flagged", True, mt, all(mt.values()) and len(mt) == 2)


def wait_for(fn, timeout):
    t_end = time.monotonic() + timeout
    while time.monotonic() < t_end:
        r = fn()
        if r:
            return r
        time.sleep(POLL)
    return None


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep, P)
    lat = []
    try:
        n = 0
        for _ in range(H2_ROUNDS):
            for _ in range(H2_BATCH):
                st.append("h2", entry("h2", n))
                n += 1
            t_last = time.monotonic()
            m = st.storage("h2")
            ok = wait_for(lambda: st.verify("h2", m)["accepted"], 3 * P)
            lat.append({"accepted": bool(ok), "s": time.monotonic() - t_last})
    finally:
        st.close()
    wit, ver = st.witness(), st.verdicts()
    keep(out, st, lat)
    R.raw.update(latency_s=[round(x["s"], 4) for x in lat], max_latency_s=max(x["s"] for x in lat))
    R.check("H2: every honest manifest is accepted within P + TAU_A = %.2f s of its last append (honest_accept)" %
            (P + TAU_A), {"accepted": H2_ROUNDS, "max_s": "<= %.2f" % (P + TAU_A)},
            {"accepted": sum(x["accepted"] for x in lat), "max_s": round(R.raw["max_latency_s"], 4)},
            all(x["accepted"] for x in lat) and R.raw["max_latency_s"] <= P + TAU_A)
    R.check("no fork alarm on an honest log", 0, sum(1 for r in wit if r["kind"] == "fork"),
            not [r for r in wit if r["kind"] == "fork"])
    check_reconcile(R, reconcile.reconcile(ver, wit))


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep, P)
    trials = []
    try:
        for j, delay in enumerate(H3_DELAYS):
            log = "w-%d" % j
            for i in range(3):
                st.append(log, entry(log, i))
            ta = time.monotonic_ns()
            honest = st.storage(log)
            time.sleep(delay)
            fake = [entry(log, i, fake=True) for i in range(3)]
            st.rewrite(log, fake)
            tr = time.monotonic_ns()
            seen = wait_for(lambda: [r for r in st.witness() if r["log"] == log and r["t"] is not None and r["t"] > tr],
                            3 * P)
            trials.append({"log": log, "delay_s": delay, "ta": ta, "tr": tr, "next_witness_record": bool(seen),
                           "fake": st.verify(log, fake), "honest": st.verify(log, honest),
                           "honest_head": chain.head_of(honest), "fake_head": chain.head_of(fake)})
    finally:
        st.close()
    wit, ver = st.witness(), st.verdicts()
    keep(out, st, trials)
    rows, consistent, windows = [], True, []
    for t in trials:
        recs = sorted([r for r in wit if r["log"] == t["log"] and r["t"] is not None], key=lambda r: r["seq"])
        before = any(r["kind"] == "anchor" and r["t"] < t["tr"] for r in recs)
        after_ta = [r for r in recs if r["t"] >= t["ta"]]
        win = (after_ta[0]["t"] - t["ta"]) / 1e9 if after_ta else None
        ok = t["next_witness_record"] and t["fake"]["accepted"] == (not before) and (
            not t["honest"]["accepted"] or before)
        consistent = consistent and ok
        windows.append(win)
        rows.append({"delay_s": t["delay_s"], "rewrite_after_append_s": round((t["tr"] - t["ta"]) / 1e9, 4),
                     "first_witness_record_after_append_s": None if win is None else round(win, 4),
                     "anchored_before_rewrite": before, "fake_accepted": t["fake"]["accepted"],
                     "honest_accepted": t["honest"]["accepted"],
                     "witness_kinds": [r["kind"] for r in recs], "consistent": ok})
    R.raw.update(trials=rows, max_window_s=max(w for w in windows if w is not None) if any(windows) else None)
    n_acc = sum(1 for r in rows if r["fake_accepted"])
    R.check("H3: a rewrite before the first anchor IS accepted, a rewrite after it is not, in every trial "
            "(rewrite_before_anchor_window: the honest limit)", "consistent in all %d trials" % len(rows),
            [(r["delay_s"], r["anchored_before_rewrite"], r["fake_accepted"]) for r in rows], consistent)
    R.check("non-vacuity: both outcomes occur", {"accepted": ">= 1", "rejected": ">= 1"},
            {"accepted": n_acc, "rejected": len(rows) - n_acc}, 0 < n_acc < len(rows))
    R.check("H3: the exposure window (append -> first anchor) is <= P + TAU_W = %.2f s" % (P + TAU_W),
            "<= %.2f" % (P + TAU_W), R.raw["max_window_s"], all(w is not None and w <= P + TAU_W for w in windows))
    check_reconcile(R, reconcile.reconcile(ver, wit))


def h4(ctx, out, rep, R):
    fired = {}
    for name, flags in (("a_current_head", ["--current-head"]), ("b_writer_heads", ["--writer-heads"])):
        st = Stack(ctx, "r%d-h4%s" % (rep, name[0]), 0, flags)
        try:
            for i in range(10):
                st.append("main", entry("main", i))
            st.anchor_now("main")
            fake = [entry("main", i, fake=True) for i in range(10)]
            if name.startswith("a"):
                st.rewrite("main", fake)
            else:
                st.publish("main", chain.head_of(fake))
            v = st.verify("main", fake)
            w = st.anchor_now("main") if name.startswith("a") else None
        finally:
            st.close()
        wit, ver = st.witness(), st.verdicts()
        keep(out, st)
        rc = reconcile.reconcile(ver, wit)
        fires = v["accepted"] and not rc["ok"] and len(rc["accepted_unanchored"]) == 1
        fired[name] = {"config": st.config, "fabricated_accepted": v["accepted"], "why": v["why"],
                       "flagged": rc["accepted_unanchored"], "witness_on_rewritten_storage": (w or {}).get("kind"),
                       "fires": fires}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H4 CONTROL %s fires: the fabricated log is accepted and the reconciliation against the witness's own "
                "log flags it (%s)" % (name, "no_anchor_rollback_breaks" if name.startswith("a")
                                       else "self_signed_breaks"),
                {"accepted": True, "flagged": 1}, {k: v for k, v in f.items() if k != "config"}, f["fires"])


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
    txt = PREREG.read_text() if PREREG.exists() else ""
    st = re.search(r"^CALIBRATION-STATUS: (\w+)\s*$", txt, re.M)
    vals = {k: float(v) for k, v in re.findall(r"^((?:TAU|L)_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"TAU_A": TAU_A, "TAU_W": TAU_W}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC27Chain.lean"]
    return {
        "prereg_id": PREREG_ID, "kind": args.kind, "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"), "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--untracked-files=all", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "model_sha256": {m: sha(REPO / m) for m in models},
        "calibration": calibration(),
        "uname_r": platform.release(), "uname_a": " ".join(platform.uname()), "python": sys.version,
        "python_executable": sys.executable, "nproc": os.cpu_count(), "uid": os.getuid(),
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); witness and runner stamps on one host",
        "constants": {k: globals()[k] for k in ("P", "H1_ENTRIES", "H2_ROUNDS", "H2_BATCH", "H3_TRIALS", "H3_DELAYS",
                                                 "POLL", "LIFETIME", "WALL_LIMIT", "TAU_A", "TAU_W")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc27-run-")
    if stale:
        problems.append("processes of an earlier sc27 run still alive: %s" % [e["pid"] for e in stale])
    if args.kind == "evidence":
        if m["git_status_harness_and_prereg"]:
            problems.append("evidence run needs committed, unmodified harness and prereg files")
        c = m["calibration"]
        if c["status"] != "FIXED":
            problems.append("prereg calibration status is %s, not FIXED (prereg §3.0)" % c["status"])
        for k, v in c["harness_values"].items():
            if c["prereg_values"].get(k) != float(v):
                problems.append("harness %s %s != prereg %s" % (k, v, c["prereg_values"].get(k)))
    return problems


def summary_md(m, verdicts, results):
    lines = ["# SC-27 anchored evidence chain (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TAU_A = %s s, TAU_W = %s s" % (m["calibration"]["status"], TAU_A, TAU_W),
             "- kernel: `%s`, python `%s`" % (m["uname_r"], m["python"].split()[0]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | kind | reps passed | verdict |", "|---|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %s | %d/%d | %s |" % (h, "NEGATIVE_CONTROL" if h in CONTROLS else "claim",
                                                     v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Key measurements per repetition", ""]
    for r in results:
        raw, s = r["raw"], ""
        if r["hyp"] == "H1":
            s = "tamper results %s" % raw.get("results")
        elif r["hyp"] == "H2":
            s = "max time to acceptance %s s" % raw.get("max_latency_s")
        elif r["hyp"] == "H3":
            s = "max window %s s; (delay, anchored before rewrite, rewrite accepted): %s" % (
                raw.get("max_window_s"), [(t["delay_s"], t["anchored_before_rewrite"], t["fake_accepted"])
                                          for t in raw.get("trials", [])])
        else:
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        lines.append("- %s rep %d: %s" % (r["hyp"], r["rep"], s))
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
    ap = argparse.ArgumentParser(description="SC-27 anchored evidence chain check (unprivileged).")
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
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok, "negative_control": h in CONTROLS,
                  "verdict": "NOT-RUN" if infra else "PASS" if len(rs) == args.reps and n_ok == args.reps else "FAIL"}
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
