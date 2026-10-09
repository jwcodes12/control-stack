#!/usr/bin/env python3
"""SC-08 DEFENSIVE application-allowlisting check (unprivileged). Preregistration: prereg/SC08-EXEC-ALLOWLIST.md
(PREREG-SC08-EXEC-v1).

Defensive reference test on one Linux host. A trusted launcher is the ONLY interface through which a benign scripted
agent (this runner) runs programs. It hashes the bytes it read from the opened program and script, checks digest
allowlists (an allowlisted interpreter must come with an allowlisted script; no REPL), pins the script (copies the
hashed bytes into a launcher-owned 0700 directory under its digest) and runs the interpreter from its already-hashed
fd (fexecve). Every program is a benign script that prints a line and appends its own code's SHA-256 to a sentinel
file. This does NOT test kernel-level enforcement: an agent with a shell could exec directly; here the launcher is the
only interface (the complete-mediation premise). Each hypothesis is repeated --reps times on fresh processes:

  H1 only allowlisted digests ever run (launcher log and the programs' own sentinel records); content in the writable
     staging directory runs only if its digest is allowlisted                (safe_of_sound / sc08_safe, honest_execs,
                                                                              digest_design_needs_no_noexec)
  H2 content swapped at the requested path between check and exec never runs (deployed half of
     path_allowlist_toctou_breaks)
  H3 the interpreter with a non-allowlisted script, and without a script (REPL), is refused
                                     (deployed halves of interpreter_loophole_breaks, interpreter_repl_breaks)
  H4 usefulness: allowlisted programs run within L_RUN
  H5 NEGATIVE_CONTROL: path-based allowlist (the swapped content runs); interpreter loophole (unchecked script and REPL
     run) -> detected   (path_allowlist_toctou_breaks, interpreter_loophole_breaks, interpreter_repl_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets and files in a fresh
/var/tmp/sc08-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
import threading
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC08-EXEC-ALLOWLIST.md"
PREREG_ID = "PREREG-SC08-EXEC-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5"]
CONTROLS = {"H5"}
INTERP = os.path.realpath("/bin/python3")

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
DELAY = 0.3                 # s, launcher check-to-exec test hook (H2, H5a)
SWAP_AT = 0.1               # s after the request, the harness swaps the file (H2, H5a)
H2_TRIALS = 3
H4_RUNS = 30
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_RUN = 1.05                # s, H4: one allowlisted run, request to reply (calibrated)

SCRIPT = '''import hashlib, json, os, time
NAME = %r
me = open(__file__, "rb").read()
with open(os.environ["SC08_SENTINEL"], "a") as fh:
    fh.write(json.dumps({"name": NAME, "self_sha256": hashlib.sha256(me).hexdigest(), "file": __file__,
                         "pid": os.getpid(), "t": time.monotonic_ns()}) + "\\n")
print("hello from " + NAME)
'''


def script(name):
    return (SCRIPT % name).encode()


def dg(b):
    return hashlib.sha256(b).hexdigest()


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
        self.work = Path(tempfile.mkdtemp(prefix="sc08-run-", dir="/var/tmp"))
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


def rpc(path, obj, timeout=30.0):
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
    """installed scripts (bin), writable staging, launcher"""

    def __init__(self, ctx, tag, flags=(), delay=0.0):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.bin, self.staging = d / "bin", d / "staging"
        self.bin.mkdir()
        self.staging.mkdir()
        for n in ("hello_a", "hello_b", "hello_c"):
            p = self.bin / (n + ".py")
            p.write_bytes(script(n))
            p.chmod(0o400)
        self.bin.chmod(0o500)   # installed programs: not writable (conceptually the agent cannot change them)
        self.allow = {
            "interpreters": [dg(open(INTERP, "rb").read())],
            "scripts": sorted(dg(script(n)) for n in ("hello_a", "hello_b", "hello_c")),
            "interpreter_paths": [INTERP],
            "script_paths": [str(self.bin / (n + ".py")) for n in ("hello_a", "hello_b", "hello_c")] +
                            [str(self.staging / "app.py")],   # path allowlist (control only): includes a staging path
        }
        (d / "allowlist.json").write_text(json.dumps(self.allow, indent=1))
        self.sentinel, self.log = d / "sentinel.jsonl", d / "launcher.jsonl"
        lp = self._spawn("launcher", ctx.script("launcher.py", "--dir", d, "--allowlist", d / "allowlist.json",
                                                "--pin-dir", d / "launcher-pins", "--out", d / "programs.out",
                                                "--sentinel", self.sentinel, "--log", self.log,
                                                "--check-exec-delay", delay, "--lifetime", LIFETIME, *flags))
        self.config = read_tag(lp, "READY")["config"]
        self.replies = []

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def run(self, program, script_path):
        r = rpc(self.d / "agent.sock", {"op": "run", "program": program,
                                        "script": None if script_path is None else str(script_path)})
        self.replies.append(r)
        return r

    def stage(self, name, data):
        p = self.staging / name
        tmp = self.staging / ("." + name + ".tmp")
        tmp.write_bytes(data)
        os.rename(str(tmp), str(p))
        return p

    def sentinels(self):
        return reconcile.load_jsonl(str(self.sentinel))

    def launcher_log(self):
        return reconcile.load_jsonl(str(self.log))

    def reconcile(self):
        ev = (self.allow, self.launcher_log(), self.sentinels())
        return reconcile.reconcile(*ev), ev

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
        try:
            self.bin.chmod(0o700)
        except OSError:
            pass


def keep(out, st, extra=None):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.sentinel, st.log, st.d / "allowlist.json", st.d / "programs.out"):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    with open(str(d / "client.json"), "w") as fh:
        json.dump({"replies": st.replies, "extra": extra}, fh, default=str)


def check_reconcile(R, rc, name="reconciliation"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every sentinel (the code that actually ran) and every launcher execution is allowlisted; one sentinel "
            "per execution (safe_of_sound)" % name, {"defects": [], "consistent": True},
            {"executions": rc["executions"], "sentinels": rc["sentinel_records"], "consistent": rc["consistent"],
             "defects": rc["defects"]}, rc["ok"])


def swap_trial(st, path, a_bytes, b_bytes):
    """request a run of `path` holding A; SWAP_AT s later replace it with B; return what ran"""
    st.stage(path.name, a_bytes)
    box = {}
    th = threading.Thread(target=lambda: box.update(r=st.run(INTERP, path)))
    t_req = time.monotonic_ns()
    th.start()
    time.sleep(SWAP_AT)
    st.stage(path.name, b_bytes)
    t_swap = time.monotonic_ns()
    th.join(timeout=20)
    return {"reply": box.get("r"), "t_req": t_req, "t_swap": t_swap}


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        res = {}
        for n in ("hello_a", "hello_b", "hello_c"):
            res[n] = st.run(INTERP, st.bin / (n + ".py"))
        res["staging copy of allowlisted content"] = st.run(INTERP, st.stage("copy_a.py", script("hello_a")))
        res["staging non-allowlisted script"] = st.run(INTERP, st.stage("other.py", script("other")))
        res["non-allowlisted program (/bin/sh)"] = st.run("/bin/sh", st.bin / "hello_a.py")
        sent = st.sentinels()
        rc, ev = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    dec = {k: (v.get("decision"), v.get("why")) for k, v in res.items()}
    R.raw.update(decisions=dec, sentinel_names=[s["name"] for s in sent])
    exp = {"hello_a": ("executed", None), "hello_b": ("executed", None), "hello_c": ("executed", None),
           "staging copy of allowlisted content": ("executed", None),
           "staging non-allowlisted script": ("refused", "script digest not allowlisted"),
           "non-allowlisted program (/bin/sh)": ("refused", "program digest not allowlisted")}
    R.check("decisions: allowlisted digests run wherever they are stored; anything else is refused "
            "(digest_design_needs_no_noexec)", exp, dec, dec == exp and all(res[k].get("rc") == 0 for k in
                                                                          ("hello_a", "hello_b", "hello_c")))
    R.check("the programs' own sentinel records: exactly hello_a, hello_b, hello_c, hello_a (honest_execs)",
            ["hello_a", "hello_b", "hello_c", "hello_a"], [s["name"] for s in sent],
            [s["name"] for s in sent] == ["hello_a", "hello_b", "hello_c", "hello_a"])
    check_reconcile(R, rc)
    mt = reconcile.mutation_selftest(*ev)
    R.check("reconciliation sensitivity: each injected defect is flagged", True, mt, all(mt.values()) and len(mt) == 4)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep, delay=DELAY)
    trials = []
    try:
        A, B = script("hello_a"), script("swapped")
        for i in range(H2_TRIALS):
            trials.append(swap_trial(st, st.staging / "app.py", A, B))
        st.stage("app.py", B)
        pre = st.run(INTERP, st.staging / "app.py")
        sent = st.sentinels()
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st, trials)
    log = [r for r in st.launcher_log() if r.get("decision") == "executed"]
    valid = [t["reply"] is not None and t["reply"].get("t_check", 0) < t["t_swap"] < t["reply"].get("t_exec", 0)
             for t in trials]
    ran = [s["self_sha256"] for s in sent]
    R.raw.update(valid_timing=valid, ran=[r[:12] for r in ran], pre_swapped=pre.get("why"))
    R.check("each swap happened after the launcher's check and before its exec (the trial is valid)",
            [True] * H2_TRIALS, valid, all(valid))
    R.check("H2: the swapped content never ran; the pinned, checked content ran instead (path_allowlist_toctou_breaks "
            "deployed half)", {"ran": [dg(A)[:12]] * H2_TRIALS}, {"ran": [r[:12] for r in ran]},
            ran == [dg(A)] * H2_TRIALS and dg(B) not in ran and len(log) == H2_TRIALS)
    R.check("content already swapped before the request is refused", "script digest not allowlisted", pre.get("why"),
            pre.get("why") == "script digest not allowlisted")
    check_reconcile(R, rc)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    try:
        r1 = st.run(INTERP, st.stage("other.py", script("other")))
        r2 = st.run(INTERP, None)
        sent = st.sentinels()
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    R.raw.update(non_allowlisted_script=r1.get("why"), repl=r2.get("why"))
    R.check("H3: interpreter with a non-allowlisted script refused (interpreter_loophole_breaks deployed half); "
            "interpreter without a script refused (interpreter_repl_breaks deployed half)",
            ["script digest not allowlisted", "interpreter without a script (REPL) refused"],
            [r1.get("why"), r2.get("why")],
            [r1.get("why"), r2.get("why")] == ["script digest not allowlisted",
                                               "interpreter without a script (REPL) refused"] and not sent)
    check_reconcile(R, rc)


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    lat = []
    try:
        for i in range(H4_RUNS):
            n = ("hello_a", "hello_b", "hello_c")[i % 3]
            t0 = time.monotonic()
            r = st.run(INTERP, st.bin / (n + ".py"))
            lat.append({"ok": r.get("decision") == "executed" and r.get("rc") == 0, "s": time.monotonic() - t0})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    ls = sorted(x["s"] for x in lat)
    okn = sum(x["ok"] for x in lat)
    R.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 2), "max": round(ls[-1] * 1e3, 2)},
                 max_latency_s=ls[-1])
    R.check("H4: all %d allowlisted runs succeed, each within L_RUN = %.2f s" % (H4_RUNS, L_RUN),
            {"ok": H4_RUNS, "max_s": "<= %.2f" % L_RUN}, {"ok": okn, "latency_ms": R.raw["latency_ms"]},
            okn == H4_RUNS and ls[-1] <= L_RUN and rc["sentinel_records"] == H4_RUNS)
    check_reconcile(R, rc)


def h5(ctx, out, rep, R):
    # (a) path-based allowlist: the swapped content runs
    st = Stack(ctx, "r%d-h5a" % rep, ["--by-path"], delay=DELAY)
    try:
        A, B = script("hello_a"), script("swapped")
        trials = [swap_trial(st, st.staging / "app.py", A, B) for _ in range(2)]
        sent = st.sentinels()
        rc_a, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st, trials)
    ran = [s["self_sha256"] for s in sent]
    fa = ran == [dg(B)] * 2 and not rc_a["ok"] and len(rc_a["defects"]) == 2
    R.raw["a"] = {"config": st.config, "ran": [r[:12] for r in ran], "defects": rc_a["defects"]}
    R.check("H5a CONTROL fires: with a path allowlist the content swapped in after the check runs, and the programs' "
            "own sentinels flag it (path_allowlist_toctou_breaks)", {"ran": [dg(B)[:12]] * 2, "flagged": 2},
            {"ran": [r[:12] for r in ran], "flagged": len(rc_a["defects"])}, fa)
    # (b) interpreter loophole: unchecked script, and a REPL
    st = Stack(ctx, "r%d-h5b" % rep, ["--no-script-check"])
    try:
        r1 = st.run(INTERP, st.stage("other.py", script("other")))
        r2 = st.run(INTERP, None)
        rc_b, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    whys = sorted({str(d.get("why")) for d in rc_b["defects"]})
    fb = (r1.get("decision") == "executed" and r2.get("decision") == "executed" and not rc_b["ok"] and
          any("not allowlisted" in w for w in whys) and any("without a script" in w for w in whys))
    R.raw["b"] = {"config": st.config, "unchecked_script": r1.get("decision"), "repl": r2.get("decision"),
                  "defects": rc_b["defects"]}
    R.check("H5b CONTROL fires: with script checking off, a non-allowlisted script and a REPL both run and are flagged "
            "(interpreter_loophole_breaks, interpreter_repl_breaks)", {"both executed": True, "both flagged": True},
            {"executed": [r1.get("decision"), r2.get("decision")], "why": whys}, fb)


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
    vals = {k: float(v) for k, v in re.findall(r"^((?:TAU|L)_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"L_RUN": L_RUN}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC08Exec.lean"]
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
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); one host",
        "interpreter": {"path": INTERP, "sha256": dg(open(INTERP, "rb").read())},
        "constants": {k: globals()[k] for k in ("DELAY", "SWAP_AT", "H2_TRIALS", "H4_RUNS", "LIFETIME", "WALL_LIMIT",
                                                 "L_RUN")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc08-run-")
    if stale:
        problems.append("processes of an earlier sc08 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-08 application allowlisting (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_RUN = %s s" % (m["calibration"]["status"], L_RUN),
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
        if r["hyp"] == "H4":
            s = "latency ms %s" % raw.get("latency_ms")
        elif r["hyp"] == "H2":
            s = "valid swaps %s, ran %s" % (raw.get("valid_timing"), raw.get("ran"))
        elif r["hyp"] == "H5":
            s = "a ran %s; b executed %s/%s" % (raw.get("a", {}).get("ran"), raw.get("b", {}).get("unchecked_script"),
                                               raw.get("b", {}).get("repl"))
        else:
            s = "decisions %s" % (raw.get("decisions") or [raw.get("non_allowlisted_script"), raw.get("repl")])
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
    ap = argparse.ArgumentParser(description="SC-08 application allowlisting check (unprivileged).")
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
