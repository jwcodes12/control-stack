#!/usr/bin/env python3
"""SC-12 session-lineage check (root required). Preregistration: prereg/SC12-LINEAGE.md (PREREG-SC12-LINEAGE-v1).

Defensive operational test with benign workloads: a session controller puts everything a session starts (child
processes, a session-detached daemon, and jobs from its own trusted scheduler) under the session, and ending the
session leaves nothing behind. Each hypothesis repeats --reps times on fresh sessions:

  H1 end-session leaves no process: zero live session-UID processes within KILL_BOUND of end-session (independent
     /proc scan), no /proc entry within REAP_BOUND; registrations for the ended session are refused.
  H2 no job fires after end-session: a job registered for after the end (and one claiming another active session,
     which the deployed scheduler ignores) is cancelled; no fire event and no sentinel after the end.
  H3 usefulness: during the session, registered jobs fire on time (scheduler lateness <= FIRE_TOL), as the session
     UID, inside the session cgroup (job-written sentinel within SENTINEL_TOL).
  H4 controls, each weakening one check, and each must be DETECTED by the H1/H2 observations:
     (a) foreign registration (claim honoured) -> a job created by the ended session fires afterwards
         (`foreign_registration_survives`);
     (b) registry bypass (helper started by the harness without placement) -> survives end-session
         (`registry_bypass_survives`);
     (c) parent-only revocation (kill the top process, not cgroup.kill) -> descendants survive
         (`parent_only_revocation_survives`).
Receipts go to --out (must not exist). UIDs are bare numbers 23901..23904; no accounts; no host cron/at/systemd.
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
from scheduler import Refused, Scheduler  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC12-LINEAGE.md"
PREREG_ID = "PREREG-SC12-LINEAGE-v1"
TOP = "sc12-test"
UID_A, UID_B = 23901, 23902
ALL_UIDS = (23901, 23902, 23903, 23904)
HYPS = ["H1", "H2", "H3", "H4"]

# Preregistered constants (prereg §3). Changing any of them needs a new prereg ID.
CHILDREN = 3                 # agent tree: parent + 3 children + 3 grandchildren + 1 daemon = 8 processes
TREE_N = 1 + 3 + 3 + 1
END_AFTER = 0.8              # s after READY, end-session
EARLY_JOB = 0.3              # s, fires during the session
LATE_JOB = 1.5               # s, due after the end (must be cancelled)
H3_JOBS = (0.3, 0.6, 0.9)    # s
KILL_BOUND = 1.0             # s, zero live processes after end-session
REAP_BOUND = 5.0             # s, no /proc entry at all
FIRE_TOL = 0.25              # s, scheduler lateness
SENTINEL_TOL = 1.0             # s, job-written sentinel after its due time (includes interpreter start)
POST_DUE = 0.7               # s, wait after the latest due time before concluding "never fired"
LIFETIME = 20.0              # s, every workload process exits by itself
READY_TIMEOUT = 10.0
WALL_LIMIT = 115             # s


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
        self.work = Path(tempfile.mkdtemp(prefix="sc12-run-", dir="/var/tmp"))
        self.work.chmod(0o755)
        code = self.work / "code"
        code.mkdir(mode=0o755)
        shutil.copy2(str(HERE / "workloads.py"), str(code / "workloads.py"))
        (code / "workloads.py").chmod(0o644)
        self.wl, self.py = code / "workloads.py", sys.executable

    def sched(self, tag, claim=False):
        d = self.work / tag
        d.mkdir(mode=0o755)
        return Scheduler(self.cg, d, self.wl, self.py, claim_mode=claim)

    def agent_argv(self, sched, jobs, claim=""):
        return [self.py, "-I", "-S", str(self.wl), "agent", "--sock", sched.sock_path, "--jobs",
                ",".join(str(j) for j in jobs), "--claim", claim, "--children", str(CHILDREN), "--daemon",
                "--lifetime", str(LIFETIME)]


def read_ready(p):
    t0 = time.monotonic()
    while time.monotonic() - t0 < READY_TIMEOUT:
        line = p.stdout.readline()
        if not line:
            break
        if line.startswith(b"READY "):
            return json.loads(line[6:])
    raise RuntimeError("workload did not report READY")


def in_session(sched, name, uid):
    """every live process of uid is in the session cgroup (independent /proc scan)"""
    want = "0::" + sched.cg.cgpath(sched.sessions[name]["path"])
    ents = [e for e in cgctl.proc_scan({uid}) if e["state"] not in ("Z", "X")]
    return all(e["cgroup"] == want for e in ents), len(ents)


def sentinel(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return None


def teardown(ctx, sched, R):
    sched.close()
    for name, s in sched.sessions.items():
        if s["path"].exists():
            R.raw.setdefault("destroy", {})[name] = ctx.cg.destroy(s["path"])
    for u in ALL_UIDS:
        if cgctl.live(cgctl.proc_scan({u})):
            R.raw.setdefault("kill_uid", {})[u] = cgctl.kill_uid(u, ALL_UIDS)


# ---------------------------------------------------------------- hypotheses
def h1(ctx, rep, R):
    s = ctx.sched("h1-%d" % rep)
    try:
        s.start_session("A", UID_A)
        p = s.launch_in("A", ctx.agent_argv(s, [EARLY_JOB, LATE_JOB]), stdout=subprocess.PIPE)
        ready = read_ready(p)
        ok, n = in_session(s, "A", UID_A)
        R.check("every live session-UID process is in the session cgroup", True, [ok, n], ok and n >= TREE_N)
        time.sleep(END_AFTER)
        t_end = s.end("A")
        g = cgctl.wait_gone({UID_A}, t_end, REAP_BOUND, reap=lambda: [q.poll() for q in s.popens])
        R.raw.update(ready=ready, gone=g)
        R.check("zero live session-UID processes within KILL_BOUND", "<= %s s" % KILL_BOUND, g["live_zero_s"],
                g["live_zero_s"] is not None and g["live_zero_s"] <= KILL_BOUND)
        R.check("no /proc entry within REAP_BOUND", "<= %s s" % REAP_BOUND, g["all_zero_s"],
                g["all_zero_s"] is not None and g["all_zero_s"] <= REAP_BOUND)
        try:
            s.register(UID_A, 0.1)
            refused = False
        except Refused:
            refused = True
        R.check("registration for the ended session refused", True, refused, refused)
    finally:
        teardown(ctx, s, R)


def h2(ctx, rep, R):
    s = ctx.sched("h2-%d" % rep)
    try:
        s.start_session("A", UID_A)
        s.start_session("B", UID_B)  # an active foreign session the agent tries to claim
        p = s.launch_in("A", ctx.agent_argv(s, [EARLY_JOB, LATE_JOB], claim="B"), stdout=subprocess.PIPE)
        ready = read_ready(p)
        time.sleep(END_AFTER)
        t_end = s.end("A")
        t_end_wall = s.sessions["A"]["t_end_wall"]
        latest_due = max(j["due"] for j in s.jobs)
        time.sleep(max(0.0, latest_due + POST_DUE - time.monotonic()))
        jobs = [dict(j) for j in s.jobs]
        R.raw.update(ready=ready, jobs=jobs, log=s.log)
        mine = [j for j in jobs if j["requester_uid"] == UID_A]
        R.check("both jobs registered under the caller's own session (claim ignored)", ["A", "A"],
                [j["session"] for j in mine], len(mine) == 2 and all(j["session"] == "A" for j in mine))
        early = [j for j in mine if j["fired_at"] is not None and j["fired_at"] < t_end]
        R.check("non-vacuity: the early job fired during the session", 1, len(early), len(early) == 1)
        after = [e for e in s.log if e["kind"] == "fire" and e["requester_uid"] == UID_A and e["t"] >= t_end]
        R.check("no fire of a session-A job after end-session (scheduler log)", 0, len(after), not after)
        late = [j for j in mine if j["fired_at"] is None]
        R.check("the job due after the end was cancelled", ["cancelled"], [j["state"] for j in late],
                len(late) == 1 and late[0]["state"] == "cancelled")
        late_sent = [sentinel(j["sentinel"]) for j in mine]
        post = [x for x in late_sent if x and x["t"] >= t_end_wall]
        R.check("no job sentinel written after end-session", 0, len(post), not post)
    finally:
        teardown(ctx, s, R)


def h3(ctx, rep, R):
    s = ctx.sched("h3-%d" % rep)
    try:
        s.start_session("A", UID_A)
        want_cg = "0::" + ctx.cg.cgpath(s.sessions["A"]["path"])
        p = s.launch_in("A", ctx.agent_argv(s, list(H3_JOBS)), stdout=subprocess.PIPE)
        ready = read_ready(p)
        latest_due = max(j["due"] for j in s.jobs)
        time.sleep(max(0.0, latest_due + SENTINEL_TOL - time.monotonic()))
        fires = [e for e in s.log if e["kind"] == "fire"]
        regs = {e["job"]: e for e in s.log if e["kind"] == "register"}
        sents = {j["id"]: sentinel(j["sentinel"]) for j in s.jobs}
        R.raw.update(ready=ready, fires=fires, sentinels=sents)
        R.check("all registered jobs fired", len(H3_JOBS), len(fires), len(fires) == len(H3_JOBS))
        late = [e["lateness_s"] for e in fires]
        R.check("scheduler lateness <= FIRE_TOL", "<= %s s" % FIRE_TOL, late, late and max(late) <= FIRE_TOL)
        good, delays = [], []
        for jid, x in sents.items():
            due_wall = regs[jid]["wall"] + regs[jid]["delay"]
            delays.append(round(x["t"] - due_wall, 4) if x else None)
            good.append(bool(x) and x["uid"] == UID_A and x["cgroup"] == want_cg and
                        0 <= x["t"] - due_wall <= SENTINEL_TOL)
        R.raw["sentinel_delay_s"] = delays
        R.check("each job ran as the session UID inside the session cgroup, sentinel within SENTINEL_TOL",
                [True] * len(H3_JOBS), good, good == [True] * len(H3_JOBS))
        t_end = s.end("A")
        g = cgctl.wait_gone({UID_A}, t_end, REAP_BOUND)
        R.check("session ends cleanly afterwards", 0, len(g["left"]), g["all_zero_s"] is not None)
    finally:
        teardown(ctx, s, R)


def h4(ctx, rep, R):
    # (a) foreign registration: the scheduler honours the claimed session
    s = ctx.sched("h4a-%d" % rep, claim=True)
    try:
        s.start_session("A", UID_A)
        s.start_session("B", UID_B)
        p = s.launch_in("A", ctx.agent_argv(s, [LATE_JOB], claim="B"), stdout=subprocess.PIPE)
        read_ready(p)
        time.sleep(END_AFTER)
        t_end = s.end("A")
        time.sleep(max(0.0, max(j["due"] for j in s.jobs) + POST_DUE - time.monotonic()))
        after = [e for e in s.log if e["kind"] == "fire" and e["requester_uid"] == UID_A and e["t"] >= t_end]
        R.raw["a"] = {"jobs": [dict(j) for j in s.jobs], "fires_after_end": after}
        R.check("(a) foreign registration: a session-A job fired after end-session -> detected", ">= 1", len(after),
                len(after) >= 1)
    finally:
        teardown(ctx, s, R)
    # (b) registry bypass: a helper started without placement survives end-session
    s = ctx.sched("h4b-%d" % rep)
    hp = None
    try:
        s.start_session("A", UID_A)
        p = s.launch_in("A", ctx.agent_argv(s, []), stdout=subprocess.PIPE)
        read_ready(p)
        hp = ctx.cg.launch_unplaced(UID_A, [ctx.py, "-I", "-S", str(ctx.wl), "helper", "--lifetime", str(LIFETIME)])
        read_ready(hp)
        t_end = s.end("A")
        time.sleep(KILL_BOUND + 0.5)
        left = [e for e in cgctl.proc_scan({UID_A}) if e["state"] not in ("Z", "X")]
        R.raw["b"] = {"left": left}
        R.check("(b) registry bypass: a live session-UID process outside the cgroup survives -> detected",
                [hp.pid], [e["pid"] for e in left], [e["pid"] for e in left] == [hp.pid])
    finally:
        if hp is not None:
            cgctl.kill_uid(UID_A, ALL_UIDS, reap=hp.poll)
            hp.wait(timeout=2)
            hp.stdout.close()
        teardown(ctx, s, R)
    # (c) parent-only revocation: killing the top process leaves descendants
    s = ctx.sched("h4c-%d" % rep)
    try:
        s.start_session("A", UID_A)
        p = s.launch_in("A", ctx.agent_argv(s, []), stdout=subprocess.PIPE)
        read_ready(p)
        s.end("A", mode="parent")
        time.sleep(KILL_BOUND + 0.5)
        p.poll()
        left = [e for e in cgctl.proc_scan({UID_A}) if e["state"] not in ("Z", "X")]
        R.raw["c"] = {"left_n": len(left)}
        R.check("(c) parent-only revocation: descendants survive -> detected", ">= %d" % (TREE_N - 1), len(left),
                len(left) >= TREE_N - 1)
    finally:
        teardown(ctx, s, R)


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4}


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
            "uids": {"A": UID_A, "B": UID_B, "reserved": list(ALL_UIDS)},
            "constants": {k: globals()[k] for k in ("CHILDREN", "TREE_N", "END_AFTER", "EARLY_JOB", "LATE_JOB",
                                                     "H3_JOBS", "KILL_BOUND", "REAP_BOUND", "FIRE_TOL", "SENTINEL_TOL",
                                                     "POST_DUE", "LIFETIME", "WALL_LIMIT")}}


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
    ap = argparse.ArgumentParser(description="SC-12 session lineage check (root).")
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
    if "H4" in per:
        per["H4"]["negative_control"] = True
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
