#!/usr/bin/env python3
"""SC-22 replication sampling (unprivileged). Preregistration: prereg/SC22-REPLICATION.md (PREREG-SC22-REPL-v1).

Defensive reference test on one Linux host (a small companion of the SC-21 sampling harness). A scripted reporter
process reports N findings per trial and misreports k of them, choosing which WITHOUT seeing the replication sample.
A separate replicator process commits to the reports, then draws a hidden uniformly random sample of B findings with
its own seed (never given to the reporter), re-runs the toy experiment on them and flags mismatches. Each hypothesis is
repeated --reps times on fresh processes:

  H1 hidden sample: the undetected fraction matches the exact C(N-k,B)/C(N,B) (exact Clopper-Pearson interval) for
     k in {1, 3, 5}; every verdict equals (sample meets the misreported set); samples are drawn after the commitment
     and are uniform                                                     (sc22_unreplicated_misreport, sc21_example)
  H2 honest reports (k = 0) are never flagged (deterministic replication)
  H3 NEGATIVE_CONTROL: a sample VISIBLE to the reporter in advance: it misreports only unsampled findings and is never
     detected (survival exactly 1)                                                         (observable_sample_nogo)
Replication checks numerical reproducibility under the frozen toy experiment, not whether a finding is correctly
interpreted (semantic; outside this test).

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/sc22-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter).
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
import analyse  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC22-REPLICATION.md"
PREREG_ID = "PREREG-SC22-REPL-v1"
HYPS = ["H1", "H2", "H3"]
CONTROLS = {"H3"}

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
N, B = 100, 10
KS = (1, 3, 5)
ALPHA = 0.01
REPS = 5
CI_LEVEL = 1 - ALPHA / (len(KS) * REPS)          # Bonferroni over k and repetitions
UNIF_ALPHA = ALPHA / REPS
EVIDENCE_SEED = "sc22-replication-evidence-v1"
LIFETIME = 60.0
READY_TIMEOUT = 10.0
WALL_LIMIT = 115
# Fixed from dry-run timing (prereg §3.0): trials per configuration per repetition.
TRIALS = 2000
SEED = None                 # set in main(): EVIDENCE_SEED for evidence runs, --seed (or random) for dry runs


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
        self.work = Path(tempfile.mkdtemp(prefix="sc22-run-", dir="/var/tmp"))
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


def rpc(path, obj, timeout=60.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(str(path))
        f = s.makefile("rwb")
        f.write((json.dumps(obj) + "\n").encode())
        f.flush()
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


class Stack:
    """replicator + reporter"""

    def __init__(self, ctx, tag):
        self.ctx, self.tag = ctx, tag
        d = self.d = ctx.work / tag
        d.mkdir()
        self.procs = []
        self.rep_log, self.rpl_log = d / "reporter.jsonl", d / "replicator.jsonl"
        read_tag(self._spawn("replicator", ctx.script("replicator.py", "--sock", d / "replicator.sock", "--log",
                                                      self.rpl_log, "--lifetime", LIFETIME)), "READY")
        read_tag(self._spawn("reporter", ctx.script("reporter.py", "--sock", d / "reporter.sock", "--replicator",
                                                    d / "replicator.sock", "--log", self.rep_log, "--lifetime",
                                                    LIFETIME)), "READY")

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def config(self, cfg, k, rep, visible=False):
        """one configuration: report (after a visible draw in the control), then replicate"""
        seeds = {w: "%s|rep%d|%s|%s" % (SEED, rep, cfg, w) for w in ("reporter", "replicator")}
        vis = None
        if visible:
            vis = rpc(self.d / "replicator.sock", {"op": "draw", "config": cfg, "trials": TRIALS, "N": N, "B": B,
                                                   "seed": seeds["replicator"]})["samples"]
        sub = rpc(self.d / "reporter.sock", {"op": "report", "config": cfg, "N": N, "k": k, "trials": TRIALS,
                                             "seed": seeds["reporter"], "visible": vis})
        res = rpc(self.d / "replicator.sock", {"op": "replicate", "config": cfg, "N": N, "B": B,
                                               "seed": seeds["replicator"]})
        return {"submit": sub, "replicate": res}

    def logs(self):
        rd = lambda p: [json.loads(l) for l in open(str(p)) if l.strip()] if p.exists() else []
        return rd(self.rep_log), rd(self.rpl_log)

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


def keep(out, st):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    import gzip
    for f in (st.rep_log, st.rpl_log):
        if f.exists():
            with open(str(f), "rb") as src, gzip.open(str(d / (f.name + ".gz")), "wb") as dst:
                shutil.copyfileobj(src, dst)


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    try:
        for k in KS:
            st.config("hidden-k%d" % k, k, rep)
        rl, pl = st.logs()
    finally:
        st.close()
    keep(out, st)
    tests, structs = {}, {}
    for k in KS:
        cfg = "hidden-k%d" % k
        tests[k] = analyse.survival_test(rl, pl, cfg, N, B, k, CI_LEVEL)
        structs[k] = analyse.structural(rl, pl, cfg)
    uni = analyse.uniformity(pl, ["hidden-k%d" % k for k in KS], N, B, UNIF_ALPHA)
    R.raw.update(tests=tests, structural=structs, uniformity=uni)
    R.check("H1: for k = 1, 3, 5 the exact undetected probability C(N-k,B)/C(N,B) lies in the two-sided Clopper-Pearson "
            "interval (level %.5f) of the observed undetected fraction (sc22_unreplicated_misreport)" % CI_LEVEL,
            {k: round(tests[k]["exact"], 5) for k in KS},
            {k: {"observed": round(tests[k]["survival"], 5), "ci": [round(x, 5) for x in tests[k]["ci"]]} for k in KS},
            all(tests[k]["contains_exact"] and tests[k]["trials"] == TRIALS for k in KS))
    R.check("structural: every verdict equals (sample meets the misreported set), flags = sample ∩ misreported, and every "
            "hidden sample was drawn after the commitment", {k: 0 for k in KS},
            {k: structs[k]["n_defects"] for k in KS}, all(structs[k]["ok"] for k in KS))
    R.check("hidden samples are uniform: every finding's inclusion count within the Bonferroni z bound",
            "|z| <= %.3f" % uni["z_crit"], round(uni["max_abs_z"], 3), uni["ok"])
    mt = analyse.mutation_selftest(rl, pl, "hidden-k3")
    R.check("analysis sensitivity: each injected defect is caught", True, mt, all(mt.values()) and len(mt) == 2)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    try:
        st.config("hidden-k0", 0, rep)
        rl, pl = st.logs()
    finally:
        st.close()
    keep(out, st)
    s = analyse.structural(rl, pl, "hidden-k0")
    t = analyse.survival_test(rl, pl, "hidden-k0", N, B, 0, CI_LEVEL)
    R.raw.update(test=t, structural=s)
    R.check("H2: honest reports are never flagged (deterministic replication)", {"detected": 0, "trials": TRIALS},
            {"detected": t["trials"] - t["undetected"], "trials": t["trials"]},
            t["undetected"] == t["trials"] == TRIALS and s["ok"])


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    try:
        for k in KS:
            st.config("visible-k%d" % k, k, rep, visible=True)
        rl, pl = st.logs()
    finally:
        st.close()
    keep(out, st)
    res = {}
    for k in KS:
        cfg = "visible-k%d" % k
        t = analyse.survival_test(rl, pl, cfg, N, B, k, CI_LEVEL)
        s = analyse.structural(rl, pl, cfg)
        res[k] = {"undetected": t["undetected"], "trials": t["trials"], "hidden_exact": round(t["exact"], 5),
                  "structural_ok": s["ok"]}
    R.raw["visible"] = res
    R.check("H3 CONTROL fires: with the sample visible in advance, every misreport avoids it and survives "
            "(survival exactly 1, against the hidden-sample value) (observable_sample_nogo)",
            {k: {"undetected": TRIALS} for k in KS}, res,
            all(res[k]["undetected"] == res[k]["trials"] == TRIALS and res[k]["structural_ok"] for k in KS))


H = {"H1": h1, "H2": h2, "H3": h3}


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
    vals = {k: float(v) for k, v in re.findall(r"^(TRIALS) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"TRIALS": TRIALS}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/EvalIntegrity.lean"]
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
        "stats_py_copied_from": {"path": "scenarios/SC-21/harness/stats.py", "sha256_at_copy": "db801867d5c3618b6a37e0921c6e7120277659aeeee94a5b54da0a2eb05091d6"},
        "constants": {k: globals()[k] for k in ("N", "B", "KS", "ALPHA", "REPS", "CI_LEVEL", "UNIF_ALPHA",
                                                 "EVIDENCE_SEED", "LIFETIME", "WALL_LIMIT", "TRIALS")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc22-run-")
    if stale:
        problems.append("processes of an earlier sc22 run still alive: %s" % [e["pid"] for e in stale])
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
    lines = ["# SC-22 replication sampling (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, TRIALS = %s per configuration; seed `%s`" % (m["calibration"]["status"], TRIALS, m.get("seed")),
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
            s = "; ".join("k=%s: observed %.4f, exact %.4f, CI [%.4f, %.4f]" % (
                k, v["survival"], v["exact"], v["ci"][0], v["ci"][1]) for k, v in raw.get("tests", {}).items())
        elif r["hyp"] == "H2":
            s = "flagged %s of %s" % (raw.get("test", {}).get("trials", 0) - raw.get("test", {}).get("undetected", 0),
                                      raw.get("test", {}).get("trials"))
        else:
            s = "visible-sample survival %s" % {k: "%s/%s" % (v["undetected"], v["trials"])
                                                for k, v in raw.get("visible", {}).items()}
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
    ap = argparse.ArgumentParser(description="SC-22 replication sampling check (unprivileged).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    ap.add_argument("--seed", default=None, help="dry runs only; evidence runs use EVIDENCE_SEED")
    args = ap.parse_args()
    global SEED
    if args.kind == "evidence" and args.seed:
        sys.exit("evidence runs use the preregistered seed (no --seed)")
    SEED = EVIDENCE_SEED if args.kind == "evidence" else (args.seed or "dry-" + os.urandom(4).hex())
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
    m["seed"] = SEED
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
