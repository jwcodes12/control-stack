#!/usr/bin/env python3
"""SC-09 exact-argument elevation broker (unprivileged). Preregistration: prereg/SC09-ELEVATION-BROKER.md
(PREREG-SC09-BROKER-v1).

Defensive reference test on one Linux host. The broker and the requesters are ordinary processes under ONE UID; the
broker identifies a caller by the kernel-reported pid (SO_PEERCRED), mapped to a requester name. The broker owns a
protected JSON config file in its private 0700 directory inside the run dir and applies only preregistered
(rule, exact-argument) changes to it; a requester never gets a handle to the file. This tests the exact-argument rule
check and the refusal to trust a claimed caller field. It does NOT test UID-level privilege separation (see the
prereg). Each hypothesis is repeated --reps times on fresh processes:

  H1 only rule-matching operations ever modify the resource (the broker's own fsync'd diff log and file hash chain,
     replayed independently)                                                            (sc09_safe)
  H2 requests with non-matching arguments (out of range, bad enum) are refused and do not change the file
  H3 a deputy request claiming to act as another requester is refused: the broker uses the peer identity, not the
     claimed one                                                               (deployed half of confused_deputy_breaks)
  H4 usefulness: in-rule requests apply within L_OP
  H5 NEGATIVE_CONTROL: a rule without argument restriction (the requester writes arbitrary benign content); a deputy
     that trusts the claimed caller (a guest's request runs as ops) -> each detected
                                            (unrestricted_elevation_breaks, confused_deputy_breaks)

Receipts go to --out, which must not exist. No root, no accounts, no sudo, no numeric UIDs, no network: Unix sockets
and files in a fresh /var/tmp/sc09-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC09-ELEVATION-BROKER.md"
PREREG_ID = "PREREG-SC09-BROKER-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5"]
CONTROLS = {"H5"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
H4_REQUESTS = 30
LIFETIME = 30.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_OP = 0.10                 # s, H4: one in-rule request, request to reply (calibrated)


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
        self.work = Path(tempfile.mkdtemp(prefix="sc09-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


class LineReader:
    def __init__(self, p):
        self.p, self.buf = p, b""

    def tag(self, tag, timeout=READY_TIMEOUT):
        t_end = time.monotonic() + timeout
        while b"\n" not in self.buf:
            rem = t_end - time.monotonic()
            if rem <= 0:
                raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, self.p.pid))
            r, _, _ = select.select([self.p.stdout.fileno()], [], [], rem)
            if not r:
                continue
            chunk = os.read(self.p.stdout.fileno(), 1 << 20)
            if not chunk:
                raise RuntimeError("EOF from pid %d (rc=%s)" % (self.p.pid, self.p.poll()))
            self.buf += chunk
        ln, self.buf = self.buf.split(b"\n", 1)
        ln = ln.decode()
        if not ln.startswith(tag + " "):
            raise RuntimeError("unexpected output: %r" % ln[:200])
        return json.loads(ln[len(tag) + 1:])


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


class Stack:
    """broker + two requesters (ops, guest)"""

    def __init__(self, ctx, tag, broker_flags=()):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.priv = d / "broker-priv"
        self.difflog = d / "diff.jsonl"
        self.req = {}
        for name in ("ops", "guest"):
            with open(str(ctx.logs / ("%s-req-%s.stderr" % (tag, name))), "wb") as se:
                p = subprocess.Popen(ctx.script("requester.py", d / "broker.sock"), stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=se, close_fds=True, bufsize=0)
            self.procs.append(p)
            self.req[name] = (p, LineReader(p))
            self.req[name][1].tag("READY")
        pids = {str(self.req["ops"][0].pid): "ops", str(self.req["guest"][0].pid): "guest"}
        self.broker = self._spawn("broker", ctx.script("broker.py", "--dir", d, "--priv", self.priv, "--requesters",
                                                       json.dumps(pids), "--difflog", self.difflog, "--lifetime",
                                                       LIFETIME, *broker_flags))
        self.info = LineReader(self.broker).tag("READY")
        self.config = self.info["config"]
        self.resource = self.priv / "config.json"

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def request(self, who, req):
        p, r = self.req[who]
        p.stdin.write((json.dumps(req) + "\n").encode())
        return r.tag("REPLY", 15)

    def resource_now(self):
        return json.load(open(str(self.resource)))

    def diff(self):
        return reconcile.load(str(self.difflog))

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
            for f in (p.stdin, p.stdout):
                if f:
                    try:
                        f.close()
                    except OSError:
                        pass


def keep(out, st):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    if st.difflog.exists():
        shutil.copy2(str(st.difflog), str(d / "diff.jsonl"))
    if st.resource.exists():
        shutil.copy2(str(st.resource), str(d / "final-config.json"))


def check_reconcile(R, rc, name="reconciliation"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every applied change matched a rule invoked by the right peer with an in-range value; replaying the "
            "diff log reproduces the file; the hash chain links to it (sc09_safe)" % name,
            {"defects": 0, "replay": True, "chain": True},
            {"applied": rc["applied"], "defects": rc["defects"], "replay_matches_file": rc["replay_matches_file"],
             "chain_linked": rc["chain_linked"], "chain_matches_file": rc["chain_matches_file"]}, rc["ok"])


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        reqs = [("ops", {"op": "apply", "rule": "set_threshold", "value": 10 + rep}),
                ("ops", {"op": "apply", "rule": "set_retries", "value": 5}),
                ("ops", {"op": "apply", "rule": "set_mode", "value": "normal"}),
                ("guest", {"op": "apply", "rule": "set_threshold", "value": 20}),       # guest: not the rule's who
                ("ops", {"op": "apply", "rule": "set_threshold", "value": 999}),        # out of range
                ("ops", {"op": "apply", "rule": "set_mode", "value": "danger"})]        # bad enum
        res = [(w, st.request(w, r)) for w, r in reqs]
        final = st.resource_now()
        rc = reconcile.reconcile(st.diff(), str(st.resource))
        mt = reconcile.mutation_selftest(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    applied = [r for _, r in res if r.get("ok")]
    R.raw.update(replies=[(w, r.get("ok"), r.get("error")) for w, r in res], final=final)
    R.check("exactly the 3 in-rule ops requests applied; guest, out-of-range and bad-enum refused", 3, len(applied),
            len(applied) == 3)
    R.check("the file reflects only the applied changes", {"threshold": 10 + rep, "retries": 5, "mode": "normal"},
            final, final == {"threshold": 10 + rep, "retries": 5, "mode": "normal"})
    check_reconcile(R, rc)
    R.check("reconciliation sensitivity: each injected defect is flagged", True, mt, all(mt.values()) and len(mt) == 3)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    try:
        before = st.resource_now()
        bad = [{"rule": "set_threshold", "value": 101}, {"rule": "set_threshold", "value": -1},
               {"rule": "set_retries", "value": 11}, {"rule": "set_mode", "value": "root"},
               {"rule": "set_threshold", "value": "50"}, {"rule": "no_such_rule", "value": 1}]
        res = [st.request("ops", dict(op="apply", **b)) for b in bad]
        after = st.resource_now()
        rc = reconcile.reconcile(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    R.raw.update(errors=[r.get("error") for r in res], before=before, after=after)
    R.check("H2: every non-matching-argument request is refused", [True] * len(bad),
            [not r.get("ok") for r in res], all(not r.get("ok") for r in res))
    R.check("H2: the protected file is unchanged and nothing was applied", {"changed": False, "applied": 0},
            {"changed": after != before, "applied": rc["applied"]}, after == before and rc["applied"] == 0)
    check_reconcile(R, rc)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    try:
        before = st.resource_now()
        r1 = st.request("guest", {"op": "apply", "rule": "set_threshold", "value": 7, "as": "ops"})
        r2 = st.request("guest", {"op": "apply", "rule": "set_mode", "value": "normal", "as": "ops"})
        after = st.resource_now()
        rc = reconcile.reconcile(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    R.raw.update(replies=[r1.get("error"), r2.get("error")], before=before, after=after)
    R.check("H3: a guest deputy request claiming to be ops is refused (the broker uses the peer identity)",
            [True, True], [not r1.get("ok"), not r2.get("ok")], not r1.get("ok") and not r2.get("ok"))
    R.check("H3: the file is unchanged", {"changed": False}, {"changed": after != before}, after == before)
    check_reconcile(R, rc)


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    lat = []
    try:
        for i in range(H4_REQUESTS):
            r = ({"rule": "set_threshold", "value": i % 101}, {"rule": "set_retries", "value": i % 11},
                 {"rule": "set_mode", "value": "safe" if i % 2 else "normal"})[i % 3]
            t0 = time.monotonic()
            res = st.request("ops", dict(op="apply", **r))
            lat.append({"ok": bool(res.get("ok")), "s": time.monotonic() - t0})
        rc = reconcile.reconcile(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    ls = sorted(x["s"] for x in lat)
    R.raw.update(latency_ms={"p50": round(ls[len(ls) // 2] * 1e3, 2), "max": round(ls[-1] * 1e3, 2)},
                 max_latency_s=ls[-1])
    R.check("H4: all %d in-rule requests apply, each within L_OP = %.2f s" % (H4_REQUESTS, L_OP),
            {"ok": H4_REQUESTS, "max_s": "<= %.2f" % L_OP},
            {"ok": sum(x["ok"] for x in lat), "latency_ms": R.raw["latency_ms"]},
            all(x["ok"] for x in lat) and ls[-1] <= L_OP and rc["applied"] == H4_REQUESTS)
    check_reconcile(R, rc)


def h5(ctx, out, rep, R):
    fired = {}
    # (a) unrestricted-elevation: a rule with no argument restriction
    st = Stack(ctx, "r%d-h5a" % rep, broker_flags=["--no-arg-check"])
    try:
        payload = "arbitrary benign content injected by the requester"
        r = st.request("ops", {"op": "apply", "rule": "set_mode", "value": payload})
        final = st.resource_now()
        rc = reconcile.reconcile(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    fired["a_unrestricted_elevation"] = {"applied": r.get("ok"), "mode_value": final.get("mode"),
                                         "defects": rc["defects"],
                                         "fires": bool(r.get("ok")) and final.get("mode") == payload and not rc["ok"]}
    # (b) confused deputy: the broker trusts the claimed caller
    st = Stack(ctx, "r%d-h5b" % rep, broker_flags=["--trust-claimed"])
    try:
        before = st.resource_now()
        r = st.request("guest", {"op": "apply", "rule": "set_threshold", "value": 7, "as": "ops"})
        after = st.resource_now()
        rc = reconcile.reconcile(st.diff(), str(st.resource))
    finally:
        st.close()
    keep(out, st)
    fired["b_confused_deputy"] = {"guest_applied": r.get("ok"), "changed": after != before, "defects": rc["defects"],
                                  "fires": bool(r.get("ok")) and after != before and not rc["ok"]}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H5 CONTROL %s fires and the independent diff-log replay detects it" % name, {"fires": True}, f,
                f["fires"])


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
            "harness_values": {"L_OP": L_OP}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC09Priv.lean"]
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
        "constants": {k: globals()[k] for k in ("H4_REQUESTS", "LIFETIME", "WALL_LIMIT", "L_OP")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc09-run-")
    if stale:
        problems.append("processes of an earlier sc09 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-09 exact-argument elevation broker (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_OP = %s s" % (m["calibration"]["status"], L_OP),
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
        elif r["hyp"] == "H5":
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        elif r["hyp"] == "H1":
            s = "final config %s" % raw.get("final")
        else:
            s = "file changed: %s" % (raw.get("after") != raw.get("before"))
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
    ap = argparse.ArgumentParser(description="SC-09 exact-argument elevation broker check (unprivileged).")
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
