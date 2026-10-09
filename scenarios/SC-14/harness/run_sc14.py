#!/usr/bin/env python3
"""SC-14 per-job multi-resource budget check (root required). Preregistration: prereg/SC14-MULTI-RESOURCE.md
(PREREG-SC14-MULTIRES-v1).

Defensive operational test with benign, bounded workloads. A job's budget is a vector metered by the kernel or the
trusted controller (jobs.py), never by the job: cumulative CPU time, memory, pids, a CPU rate per 100 ms period, and
a lease expiry. Network egress is out of scope here. Each hypothesis repeats --reps times on fresh job cgroups:

  H1 every resource's metered usage stays within its cap (+ tolerance), against three greedy jobs (CPU loop longer
     than the CPU budget; allocation twice the memory cap; more forks than the pids cap), each shown to have tried.
  H2 control (`aggregate_cap_breaks`): with only an aggregate cap (sum of per-resource fractions), a CPU-heavy job
     uses more CPU than its intended per-resource cap while the aggregate stays within the aggregate cap -> DETECTED.
  H3 the rate limit holds: CPU rate over a window <= quota/period + RATE_TOL, and throttling was active.
  H4 expiry: a job still running at its lease deadline is killed within EXP_TOL of the deadline; zero live job
     processes within KILL_BOUND of the deadline (independent /proc scan); later launches into it are refused.
  H5 usefulness: a job within every budget completes normally, unkilled, before its expiry.
Receipts go to --out (must not exist). UIDs are bare numbers 23905..23909; no accounts are created.
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import cgctl  # noqa: E402
from jobs import JobCtl, Refused  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC14-MULTI-RESOURCE.md"
PREREG_ID = "PREREG-SC14-MULTIRES-v1"
TOP = "sc14-test"
UID = 23905
ALL_UIDS = (23905, 23906, 23907, 23908, 23909)
HYPS = ["H1", "H2", "H3", "H4", "H5"]

# Preregistered constants (prereg §3). Changing any of them needs a new prereg ID.
MIB = 1024 * 1024
BUDGET = {"cpu_usec": 500000, "memory": 32 * MIB, "pids": 8, "rate_quota": 50000, "expiry_s": 10.0}
CPU_TOL_USEC = 50000         # 50 ms of CPU beyond the budget (one poll at the rate cap + kill latency)
GREEDY_CPU_S = 3.0           # wall seconds of busy loop (needs 1.0 s at 0.5 CPU to reach the 0.5 s budget)
GREEDY_MIB = 64              # twice the memory cap
GREEDY_FORKS, FORK_HOLD = 20, 1.0
AGG_CAP = 3.0                # aggregate control: sum of fractions
RATE_QUOTA = 20000           # H3: 0.2 CPU
RATE_TOL = 0.03              # CPUs
RATE_WARMUP, RATE_WINDOW = 0.3, 2.0
RATE_CPU_S = 3.0
EXPIRY_S = 1.0               # H4 lease
EXP_TOL = 0.05               # s, kill written after the deadline
KILL_BOUND = 1.0             # s after the deadline: zero live processes
REAP_BOUND = 5.0
OK_EXPIRY_S = 5.0            # H5
WAIT_EXIT = 10.0
WALL_LIMIT = 115


class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep, self.checks, self.raw, self.error = hyp, rep, [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "pass": self.passed(), "error": self.error, "checks": self.checks,
                "raw": self.raw}


class Ctx:
    def __init__(self):
        self.cg = cgctl.Cg(TOP, ALL_UIDS)
        self.work = Path(tempfile.mkdtemp(prefix="sc14-run-", dir="/var/tmp"))
        self.work.chmod(0o755)
        shutil.copy2(str(HERE / "workloads.py"), str(self.work / "workloads.py"))
        (self.work / "workloads.py").chmod(0o644)
        self.wl, self.py = self.work / "workloads.py", sys.executable

    def argv(self, *a):
        return [self.py, "-I", "-S", str(self.wl)] + [str(x) for x in a]


def finish(p, timeout=WAIT_EXIT):
    try:
        out, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        p.kill()
        out, _ = p.communicate()
    lines = out.decode(errors="replace").splitlines() if out else []
    done = [json.loads(l[5:]) for l in lines if l.startswith("DONE ")]
    return {"rc": p.returncode, "done": done[0] if done else None, "lines": len(lines)}


def wait_ready(p, timeout=10.0):
    t0 = time.monotonic()
    while time.monotonic() - t0 < timeout:
        line = p.stdout.readline()
        if not line or line.startswith(b"READY"):
            return bool(line)
    return False


def teardown(ctx, ctl, R):
    ctl.close()
    for name, j in ctl.jobs.items():
        if Path(j.path).exists():
            R.raw.setdefault("destroy", {})[name] = ctx.cg.destroy(j.path)
    for u in ALL_UIDS:
        if cgctl.live(cgctl.proc_scan({u})):
            R.raw.setdefault("kill_uid", {})[u] = cgctl.kill_uid(u, ALL_UIDS)


# ---------------------------------------------------------------- hypotheses
def h1(ctx, rep, R):
    ctl = JobCtl(ctx.cg)
    try:
        ctl.create("cpu%d" % rep, BUDGET)
        o = finish(ctl.launch("cpu%d" % rep, UID, ctx.argv("cpu", "--seconds", GREEDY_CPU_S),
                              stdout=subprocess.PIPE))
        s = ctl.stats("cpu%d" % rep)
        k = ctl.jobs["cpu%d" % rep].killed
        R.raw["cpu"] = {"out": o, "stats": s, "killed": k}
        R.check("cpu: the job tried to exceed (killed for its CPU budget, did not finish)", "cpu_budget",
                k and k["reason"], bool(k) and k["reason"] == "cpu_budget" and o["done"] is None)
        R.check("cpu: metered usage <= budget + CPU_TOL", "<= %d usec" % (BUDGET["cpu_usec"] + CPU_TOL_USEC),
                s["usage_usec"], s["usage_usec"] <= BUDGET["cpu_usec"] + CPU_TOL_USEC)
        ctl.create("mem%d" % rep, BUDGET)
        o = finish(ctl.launch("mem%d" % rep, UID, ctx.argv("mem", "--mib", GREEDY_MIB), stdout=subprocess.PIPE))
        s = ctl.stats("mem%d" % rep)
        R.raw["mem"] = {"out": o, "stats": s}
        R.check("memory: the job tried to exceed (OOM kill recorded, did not finish)", ">= 1",
                s["memory.events"].get("oom_kill"), s["memory.events"].get("oom_kill", 0) >= 1 and o["done"] is None)
        R.check("memory: memory.peak <= memory.max", "<= %d" % BUDGET["memory"], s["memory.peak"],
                s["memory.peak"] is not None and s["memory.peak"] <= BUDGET["memory"])
        ctl.create("pid%d" % rep, BUDGET)
        o = finish(ctl.launch("pid%d" % rep, UID, ctx.argv("forks", "--n", GREEDY_FORKS, "--hold", FORK_HOLD),
                              stdout=subprocess.PIPE))
        s = ctl.stats("pid%d" % rep)
        R.raw["pids"] = {"out": o, "stats": s}
        eagain = (o["done"] or {}).get("eagain", 0)
        R.check("pids: the job tried to exceed (EAGAIN on forks beyond the cap)", ">= 1", eagain, eagain >= 1)
        R.check("pids: pids.peak <= pids.max", "<= %d" % BUDGET["pids"], s["pids.peak"],
                s["pids.peak"] is not None and s["pids.peak"] <= BUDGET["pids"])
    finally:
        teardown(ctx, ctl, R)


def h2(ctx, rep, R):
    ctl = JobCtl(ctx.cg)
    try:
        ctl.create("agg%d" % rep, BUDGET, mode="aggregate", agg_cap=AGG_CAP)
        o = finish(ctl.launch("agg%d" % rep, UID, ctx.argv("cpu", "--seconds", GREEDY_CPU_S),
                              stdout=subprocess.PIPE))
        s = ctl.stats("agg%d" % rep)
        k = ctl.jobs["agg%d" % rep].killed
        R.raw.update(out=o, stats=s, killed=k)
        over = s["usage_usec"] > BUDGET["cpu_usec"] + CPU_TOL_USEC
        R.check("aggregate-only cap: CPU exceeded its intended per-resource cap -> detected",
                "> %d usec" % (BUDGET["cpu_usec"] + CPU_TOL_USEC), s["usage_usec"], over)
    finally:
        teardown(ctx, ctl, R)


def h3(ctx, rep, R):
    ctl = JobCtl(ctx.cg)
    b = dict(BUDGET, rate_quota=RATE_QUOTA, cpu_usec=2000000)
    try:
        name = "rate%d" % rep
        ctl.create(name, b)
        p = ctl.launch(name, UID, ctx.argv("cpu", "--seconds", RATE_CPU_S), stdout=subprocess.PIPE)
        wait_ready(p)
        time.sleep(RATE_WARMUP)
        j = ctl.jobs[name]
        t1, u1 = time.monotonic(), ctl.usage(j)
        time.sleep(RATE_WINDOW)
        t2, u2 = time.monotonic(), ctl.usage(j)
        rate = (u2["usage_usec"] - u1["usage_usec"]) / 1e6 / (t2 - t1)
        finish(p)
        R.raw.update(rate_cpus=round(rate, 4), throttled=[u1["nr_throttled"], u2["nr_throttled"]])
        R.check("CPU rate over the window <= quota/period + RATE_TOL", "<= %.2f" % (RATE_QUOTA / 1e5 + RATE_TOL),
                round(rate, 4), rate <= RATE_QUOTA / 1e5 + RATE_TOL)
        R.check("the rate cap was binding (nr_throttled rose)", "> 0", u2["nr_throttled"] - u1["nr_throttled"],
                u2["nr_throttled"] > u1["nr_throttled"])
    finally:
        teardown(ctx, ctl, R)


def h4(ctx, rep, R):
    ctl = JobCtl(ctx.cg)
    try:
        name = "exp%d" % rep
        ctl.create(name, dict(BUDGET, expiry_s=EXPIRY_S))
        p = ctl.launch(name, UID, ctx.argv("sleep", "--seconds", 10), stdout=subprocess.PIPE)
        j = ctl.jobs[name]
        while j.killed is None and time.monotonic() < j.deadline + 2.0:
            time.sleep(0.005)
        g = cgctl.wait_gone({UID}, j.deadline, REAP_BOUND, reap=p.poll)
        k = j.killed
        R.raw.update(killed=k, gone=g, deadline=j.deadline)
        R.check("killed for expiry", "expiry", k and k["reason"], bool(k) and k["reason"] == "expiry")
        lag = (k["t"] - j.deadline) if k else None
        R.check("kill written within EXP_TOL of the deadline", "<= %s s" % EXP_TOL, lag and round(lag, 4),
                lag is not None and 0 <= lag <= EXP_TOL)
        R.check("zero live job processes within KILL_BOUND of the deadline", "<= %s s" % KILL_BOUND,
                g["live_zero_s"], g["live_zero_s"] is not None and g["live_zero_s"] <= KILL_BOUND)
        try:
            ctl.launch(name, UID, ctx.argv("sleep", "--seconds", 1))
            refused = False
        except Refused:
            refused = True
        R.check("later launch into the expired job refused", True, refused, refused)
        finish(p)
    finally:
        teardown(ctx, ctl, R)


def h5(ctx, rep, R):
    ctl = JobCtl(ctx.cg)
    try:
        name = "ok%d" % rep
        ctl.create(name, dict(BUDGET, expiry_s=OK_EXPIRY_S))
        t0 = time.monotonic()
        o = finish(ctl.launch(name, UID, ctx.argv("ok"), stdout=subprocess.PIPE))
        el = time.monotonic() - t0
        s = ctl.stats(name)
        j = ctl.jobs[name]
        R.raw.update(out=o, stats=s, elapsed_s=round(el, 3))
        R.check("completed normally (rc 0, DONE reported)", [0, True], [o["rc"], o["done"] is not None],
                o["rc"] == 0 and o["done"] is not None)
        R.check("not killed by the controller, finished before expiry", [None, "< %s s" % OK_EXPIRY_S],
                [j.killed, round(el, 3)], j.killed is None and el < OK_EXPIRY_S)
        within = (s["usage_usec"] <= BUDGET["cpu_usec"] and s["memory.peak"] <= BUDGET["memory"] and
                  s["pids.peak"] <= BUDGET["pids"])
        R.check("metered usage within every cap", True, [s["usage_usec"], s["memory.peak"], s["pids.peak"]], within)
    finally:
        teardown(ctx, ctl, R)


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-c", "safe.directory=%s" % REPO, "-C", str(REPO)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files() if p.exists()]
    return {"prereg_id": PREREG_ID, "kind": args.kind, "argv": sys.argv, "git_commit": git("rev-parse", "HEAD"),
            "git_status_harness_and_prereg": git("status", "--porcelain", "--", *rel),
            "sha256": {r: sha(REPO / r) for r in rel}, "uname_a": " ".join(platform.uname()), "python": sys.version,
            "uid": UID, "reserved_uids": list(ALL_UIDS),
            "constants": {k: globals()[k] for k in ("BUDGET", "CPU_TOL_USEC", "GREEDY_CPU_S", "GREEDY_MIB",
                                                     "GREEDY_FORKS", "FORK_HOLD", "AGG_CAP", "RATE_QUOTA", "RATE_TOL",
                                                     "RATE_WARMUP", "RATE_WINDOW", "RATE_CPU_S", "EXPIRY_S", "EXP_TOL",
                                                     "KILL_BOUND", "REAP_BOUND", "OK_EXPIRY_S", "WALL_LIMIT")}}


def preflight(cg):
    problems = []
    if os.geteuid() != 0:
        problems.append("must run as root")
    if not (cgctl.CG_ROOT / "cgroup.controllers").exists():
        problems.append("cgroup v2 not mounted")
    if cg.top.exists():
        problems.append("%s already exists (stale run? use --cleanup-stale)" % cg.top)
    if cgctl.proc_scan(set(ALL_UIDS)):
        problems.append("processes already running under reserved UIDs")
    return problems


def cleanup_all(cg):
    rep = {"kill_uid": {}}
    for u in ALL_UIDS:
        if cgctl.proc_scan({u}):
            rep["kill_uid"][u] = cgctl.kill_uid(u, ALL_UIDS)
    rep["top"] = cg.destroy(cg.top) if cg.top.exists() else None
    rep["left_procs"] = cgctl.proc_scan(set(ALL_UIDS))
    rep["top_exists"] = cg.top.exists()
    return rep


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-14 multi-resource budget check (root).")
    ap.add_argument("--out", required=True)
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS))
    ap.add_argument("--cleanup-stale", action="store_true")
    args = ap.parse_args()
    cg = cgctl.Cg(TOP, ALL_UIDS)
    if args.cleanup_stale:
        print(json.dumps(cleanup_all(cg), indent=1, default=str))
        return 0
    hyps = [h for h in args.only.split(",") if h]
    if any(h not in HYPS for h in hyps):
        sys.exit("unknown hypothesis")
    if args.kind == "evidence" and (hyps != HYPS or args.reps != 5):
        sys.exit("evidence runs use all hypotheses and --reps 5")
    out = Path(args.out)
    if out.exists():
        sys.exit("refusing to overwrite existing --out %s" % out)
    if not out.parent.is_dir():
        sys.exit("parent of --out does not exist")
    if args.kind == "evidence" and (not PREREG.exists() or "Status: DRAFT" in PREREG.read_text()):
        sys.exit("evidence runs need the frozen prereg")
    out.mkdir()
    m = meta(args)
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    t0 = time.monotonic()
    results, infra, aborted, cleanup, ctx = [], None, None, None, None
    problems = preflight(cg)
    if args.kind == "evidence" and m["git_status_harness_and_prereg"]:
        problems.append("evidence run needs committed, unmodified harness and prereg files")
    if problems:
        infra = problems
    else:
        signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(WallLimit("wall limit")))
        signal.alarm(WALL_LIMIT)
        try:
            cg.ensure_top()
            ctx = Ctx()
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    R = Rec(h, rep)
                    t = time.monotonic()
                    try:
                        H[h](ctx, rep, R)
                    except WallLimit:
                        R.error = traceback.format_exc()
                        results.append(R.as_dict())
                        raise
                    except Exception:
                        R.error = traceback.format_exc()
                    R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                    left = cgctl.proc_scan(set(ALL_UIDS))
                    kids = [x.name for x in cg.top.iterdir() if x.is_dir()]
                    R.raw["after"] = {"left_procs": left, "cgroups": kids}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL", R.raw["elapsed_s"]),
                          flush=True)
                    if left or kids:
                        aborted = "residue after %s rep %d: procs %s cgroups %s" % (h, rep, left, kids)
                        raise RuntimeError(aborted)
        except Exception:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            cleanup = cleanup_all(cg)
            if ctx is not None:
                shutil.rmtree(str(ctx.work), ignore_errors=True)
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t0, 2)
    per = {}
    for h in hyps:
        rs = [x for x in results if x["hyp"] == h]
        n_ok = sum(x["pass"] for x in rs)
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok,
                  "verdict": "NOT-RUN" if infra else "PASS" if len(rs) == args.reps and n_ok == args.reps else "FAIL"}
    if "H2" in per:
        per["H2"]["negative_control"] = True
    cleanup_ok = cleanup is None or (not cleanup["left_procs"] and not cleanup["top_exists"])
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": cleanup_ok, "per_hypothesis": per}
    verdicts["overall"] = ("INFRA-ERROR" if infra else "PASS" if not aborted and cleanup_ok and all(
        v["verdict"] == "PASS" for v in per.values()) else "FAIL")
    dump = lambda name, obj: (out / name).write_text(json.dumps(obj, indent=1, sort_keys=True, default=str) + "\n")
    dump("meta.json", m)
    dump("verdicts.json", verdicts)
    dump("cleanup.json", cleanup)
    with open(str(out / "results.jsonl"), "w") as fh:
        for x in results:
            fh.write(json.dumps(x, sort_keys=True, default=str) + "\n")
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if uid and gid:
        for root, dirs, files in os.walk(str(out)):
            for n in [root] + [os.path.join(root, f) for f in dirs + files]:
                os.chown(n, int(uid), int(gid))
    print(json.dumps({"overall": verdicts["overall"], "per": {k: v["verdict"] for k, v in per.items()},
                      "wall_s": m["wall_s"]}))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
