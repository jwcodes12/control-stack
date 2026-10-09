#!/usr/bin/env python3
"""SC-28 cgroup v2 meter check (root required). Preregistration: prereg/SC28-CGROUP-METER.md (PREREG-SC28-CGMETER-v1).

Defensive operational test: does a trusted job controller account for every process of a job, and does "cancel
job" (revoke a lease) and HALT (stop the whole run) stop all of them? Workloads are benign and bounded (see
workloads.py). Checks, each repeated --reps times on fresh cgroups:

  H1 attribution  : a lease's whole tree, including a start_new_session daemon child, is in the lease cgroup
                    (cgroup.procs == independent /proc scan of the workload UID == the workload's own pid report).
  H2 joint cap    : (a) two leases at 50% CPU each under a run capped at 50%: combined rate over a 2.0 s window
                    <= 0.50 + 0.05 CPU, and the run's cap was binding (nr_throttled rose); (b) pids.max: a workload
                    asking for 12 children under pids.max 8 gets EAGAIN on the excess forks, alone and jointly.
  H3 revocation   : after revoke, zero live processes of that lease within 1.0 s (independent /proc scan), the other
                    lease untouched, and a later launch into the revoked lease refused.
  H4 HALT         : freeze + kill on the run: zero live workload-UID processes within 1.0 s; later launches and lease
                    creation refused.
  H5 control      : the same tree launched WITHOUT placement is invisible to the lease's accounting (while a placed
                    tree is fully visible); it is then cleaned up by UID.

Receipts go to --out, which must not exist. Nothing creates accounts: UIDs are bare numbers set with setuid.
Python 3.9 compatible (runs under the system interpreter via sudo).
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True  # never leave root-owned __pycache__ in the repo
sys.path.insert(0, str(HERE))
import meter  # noqa: E402
from meter import Limits, Meter, Refused  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC28-CGROUP-METER.md"
PREREG_ID = "PREREG-SC28-CGMETER-v1"
UID_A, UID_B, UID_UNPLACED = 23701, 23702, 23709
ALL_UIDS = tuple(meter.WORKLOAD_UIDS)
HYPS = ["H1", "H2", "H3", "H4", "H5"]

# Preregistered constants (§3 of the prereg). Changing any of them needs a new prereg ID.
TREE_ARGS = ["--children", "8", "--grandchildren", "2"]
TREE_N = 1 + 8 + 8 * 2 + 1          # parent + children + grandchildren + daemon
LIFETIME = 30.0                      # every workload process exits by itself after this
PARENT_CPU = 0.50                    # run cap, CPUs
CPU_TOL = 0.05                       # CPUs
CPU_WINDOW = 2.0                     # s
CPU_WARMUP = 0.3                     # s between both READY and the window start
CPU_SECONDS = 3.5                    # wall-clock budget of each H2a CPU loop (> warmup + window)
KILL_BOUND = 1.0                     # s, H3 and H4: zero live processes
REAP_BOUND = 5.0                     # s, no /proc entry at all (zombies included)
FREEZE_BOUND = 0.5                   # s, H4 frozen observed before kill
REFUSAL_SETTLE = 0.3                 # s, wait before the post-refusal scan
READY_TIMEOUT = 10.0
WALL_LIMIT = 115                     # s, whole run
PIDS_SMALL = 8
FORKS_REQUESTED = 12
HOLDER_CHILDREN = 3


# ---------------------------------------------------------------- independent /proc observation (no cgroup files)
def proc_scan(uids):
    """Every /proc/<pid> whose real UID is in uids. Independent of the controller: reads only /proc."""
    out = []
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/status" % d) as fh:
                status = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        uid = state = ppid = None
        for line in status.splitlines():
            if line.startswith("Uid:"):
                uid = int(line.split()[1])
            elif line.startswith("State:"):
                state = line.split()[1]
            elif line.startswith("PPid:"):
                ppid = int(line.split()[1])
        if uid not in uids:
            continue
        e = {"pid": int(d), "uid": uid, "state": state, "ppid": ppid, "sid": None, "cgroup": None}
        try:
            with open("/proc/%s/stat" % d) as fh:
                st = fh.read()
            e["sid"] = int(st[st.rindex(")") + 2:].split()[3])
            with open("/proc/%s/cgroup" % d) as fh:
                e["cgroup"] = fh.read().strip()
        except (FileNotFoundError, ProcessLookupError, ValueError):
            pass
        out.append(e)
    return out


def live(entries):
    return {e["pid"] for e in entries if e["state"] not in ("Z", "X")}


def kill_uid(uid, timeout=REAP_BOUND, reap=None):
    """SIGKILL every live process whose real UID is uid, race-free via pidfd, until none is seen in 3 consecutive
    scans. Only the reserved workload UIDs are accepted."""
    if uid not in meter.WORKLOAD_UIDS:
        raise ValueError("kill_uid refuses uid %d" % uid)
    t0, quiet, signalled = time.monotonic(), 0, 0
    while time.monotonic() - t0 < timeout:
        if reap:
            reap()
        pids = live(proc_scan({uid}))
        if not pids:
            quiet += 1
            if quiet >= 3:
                return {"ok": True, "signalled": signalled, "s": round(time.monotonic() - t0, 4)}
            time.sleep(0.01)
            continue
        quiet = 0
        for pid in pids:
            try:
                fd = os.pidfd_open(pid)
            except (ProcessLookupError, OSError):
                continue
            try:
                with open("/proc/%d/status" % pid) as fh:
                    same = any(l.startswith("Uid:") and int(l.split()[1]) == uid for l in fh)
                if same:
                    signal.pidfd_send_signal(fd, signal.SIGKILL)
                    signalled += 1
            except (FileNotFoundError, ProcessLookupError, OSError):
                pass
            finally:
                os.close(fd)
        time.sleep(0.005)
    return {"ok": False, "signalled": signalled, "left": sorted(live(proc_scan({uid})))}


def wait_gone(uids, t0, bound_live, bound_all, extra=None, reap=None):
    """Poll /proc until no live process of uids (latency from t0), then until no entry at all."""
    t_live = t_all = None
    while True:
        if reap:
            reap()
        ents = proc_scan(set(uids))
        now = time.monotonic()
        ok_extra = extra() if extra else True
        if t_live is None and not live(ents) and ok_extra:
            t_live = now - t0
        if t_live is not None and not ents:
            t_all = now - t0
            break
        if now - t0 > max(bound_all, bound_live) + 1.0:
            break
        time.sleep(0.002)
    return {"live_zero_s": None if t_live is None else round(t_live, 4),
            "all_zero_s": None if t_all is None else round(t_all, 4),
            "left": [] if t_all is not None else proc_scan(set(uids))}


# ---------------------------------------------------------------- helpers
class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep = hyp, rep
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "pass": self.passed(), "error": self.error,
                "checks": self.checks, "raw": self.raw}


class Ctx:
    def __init__(self):
        self.work = Path(tempfile.mkdtemp(prefix="sc28-run-", dir="/var/tmp"))
        self.work.chmod(0o755)
        code = self.work / "code"
        code.mkdir(mode=0o755)
        shutil.copy2(str(HERE / "workloads.py"), str(code / "workloads.py"))
        (code / "workloads.py").chmod(0o644)
        self.wl_path = code / "workloads.py"
        self.logs = self.work / "logs"
        self.logs.mkdir(mode=0o755)
        self.py = sys.executable
        self.n = 0

    def wl(self, *args):
        return [self.py, "-I", "-S", str(self.wl_path)] + [str(a) for a in args] + ["--lifetime", str(LIFETIME)]

    def log(self, tag):
        self.n += 1
        return open(str(self.logs / ("%03d-%s.stderr" % (self.n, tag))), "wb")


def read_ready(p, timeout=READY_TIMEOUT):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no READY within %.1fs from pid %d" % (timeout, p.pid))
        r, _, _ = select.select([fd], [], [], rem)
        if not r:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before READY from pid %d (rc=%s)" % (p.pid, p.poll()))
        buf += chunk
    line = buf.split(b"\n", 1)[0].decode()
    if not line.startswith("READY "):
        raise RuntimeError("unexpected workload output: %r" % line)
    return json.loads(line[6:])


def tree_pids(r):
    s = {r["parent"]} | set(r["children"]) | set(r["grandchildren"])
    if r.get("daemon"):
        s.add(r["daemon"])
    return s


def launch_unplaced(ctx, uid, argv, stderr):
    """H5 only: the same launch path minus cgroup placement (credential drop only)."""
    if uid not in meter.WORKLOAD_UIDS:
        raise ValueError(uid)

    def drop():
        os.setgroups([])
        os.setgid(uid)
        os.setuid(uid)
        os.umask(0o077)
    return subprocess.Popen(argv, preexec_fn=drop, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=stderr,
                            cwd="/", env=dict(meter.ENV), close_fds=True)


def strip_procs(s):
    s = dict(s)
    s["procs_n"] = len(s.pop("procs"))
    return s


# ---------------------------------------------------------------- hypotheses
def h1(ctx, rep, R):
    m = Meter("r%d-h1" % rep, Limits(pids_max=64))
    try:
        m.create_lease("a", Limits(pids_max=32))
        R.raw["settings"] = m.settings()
        with ctx.log("h1-a") as lf:
            p = m.launch("a", UID_A, ctx.wl("tree", *TREE_ARGS, "--cpu-children", 2, "--cpu-seconds", 2.0,
                                            "--daemon"), stderr=lf)
        r = read_ready(p)
        cg = set(m.lease_procs("a"))
        scan = proc_scan({UID_A})
        lv = live(scan)
        rep_ = tree_pids(r)
        lease_cg = meter.cgpath(m.leases["a"].path)
        R.raw.update(ready=r, cgroup_procs=sorted(cg), proc_scan=scan, stats=strip_procs(m.stats("a")))
        R.check("workload tree complete", True, r["complete"], r["complete"])
        R.check("tree size (parent+8+16+daemon)", TREE_N, len(rep_), len(rep_) == TREE_N)
        R.check("cgroup.procs == /proc scan of uid %d (live)" % UID_A, "equal sets",
                {"cg_only": sorted(cg - lv), "scan_only": sorted(lv - cg), "n_cg": len(cg), "n_scan": len(lv)},
                cg == lv)
        R.check("cgroup.procs == workload pid report", "equal sets",
                {"cg_only": sorted(cg - rep_), "report_only": sorted(rep_ - cg)}, cg == rep_)
        d = r.get("daemon")
        detached = d is not None and r.get("daemon_sid") == d and r.get("daemon_sid") != r.get("parent_sid")
        R.check("daemon child is session-detached (sid == own pid != parent sid)", True,
                {"daemon": d, "daemon_sid": r.get("daemon_sid"), "parent_sid": r.get("parent_sid")}, detached)
        R.check("daemon child is in the lease cgroup", True, d in cg, d in cg)
        wrong = [e["pid"] for e in scan if e["pid"] in lv and e["cgroup"] != "0::" + lease_cg]
        R.check("/proc/<pid>/cgroup of every uid-%d process == lease" % UID_A, [], wrong, not wrong)
        R.check("lease pids.current == tree size", TREE_N, R.raw["stats"]["pids.current"],
                R.raw["stats"]["pids.current"] == TREE_N)
    finally:
        R.raw["cleanup"] = m.close()


def h2(ctx, rep, R):
    # (a) joint CPU cap
    m = Meter("r%d-h2a" % rep, Limits(pids_max=64))
    try:
        m.create_lease("a", Limits(pids_max=8))
        m.create_lease("b", Limits(pids_max=8))
        st = m.settings()
        R.raw["a_settings"] = st
        lease_q = sum(int(st["leases"][n]["cpu.max"].split()[0]) for n in ("a", "b"))
        run_q = int(st["run"]["cpu.max"].split()[0])
        R.check("a: leases individually allow more than the run cap (sum of lease quotas > run quota)",
                "> %d" % run_q, lease_q, lease_q > run_q)
        with ctx.log("h2a-a") as la, ctx.log("h2a-b") as lb:
            pa = m.launch("a", UID_A, ctx.wl("cpu", "--seconds", CPU_SECONDS), stderr=la)
            pb = m.launch("b", UID_B, ctx.wl("cpu", "--seconds", CPU_SECONDS), stderr=lb)
        read_ready(pa)
        read_ready(pb)
        time.sleep(CPU_WARMUP)
        la_, lb_ = m.leases["a"].path, m.leases["b"].path
        s0 = [meter.cpu_usage(la_), meter.cpu_usage(lb_), meter.cpu_usage(m.path)]
        time.sleep(CPU_WINDOW)
        s1 = [meter.cpu_usage(la_), meter.cpu_usage(lb_), meter.cpu_usage(m.path)]
        dt = s1[2][0] - s0[2][0]
        ra = (s1[0][1] - s0[0][1]) / 1e6 / dt
        rb = (s1[1][1] - s0[1][1]) / 1e6 / dt
        rp = (s1[2][1] - s0[2][1]) / 1e6 / dt
        thr = s1[2][2] - s0[2][2]
        R.raw["a_window"] = {"s0": s0, "s1": s1, "dt": dt, "rate_a": ra, "rate_b": rb, "rate_run": rp,
                             "run_nr_throttled_delta": thr, "loadavg": os.getloadavg()}
        bound = PARENT_CPU + CPU_TOL
        R.check("a: combined lease CPU rate <= %.2f" % bound, "<= %.2f" % bound, round(ra + rb, 4),
                ra + rb <= bound)
        R.check("a: run-cgroup CPU rate <= %.2f" % bound, "<= %.2f" % bound, round(rp, 4), rp <= bound)
        R.check("a: run cap was binding (run nr_throttled rose in window)", ">= 1", thr, thr >= 1)
    finally:
        R.raw["a_cleanup"] = m.close()

    # (b1) pids.max on a single lease: 12 requested, limit 8 -> 7 forks succeed, 5 get EAGAIN
    m = Meter("r%d-h2b1" % rep, Limits(pids_max=PIDS_SMALL))
    try:
        m.create_lease("a", Limits(pids_max=PIDS_SMALL))
        R.raw["b1_settings"] = m.settings()
        with ctx.log("h2b1-a") as lf:
            p = m.launch("a", UID_A, ctx.wl("forks", "--n", FORKS_REQUESTED), stderr=lf)
        r = read_ready(p)
        s = strip_procs(m.stats("a"))
        R.raw["b1"] = {"ready": r, "lease": s, "run": strip_procs(m.stats())}
        R.check("b1: forks succeeded", PIDS_SMALL - 1, r["ok"], r["ok"] == PIDS_SMALL - 1)
        R.check("b1: forks refused with EAGAIN", FORKS_REQUESTED - (PIDS_SMALL - 1), r["eagain"],
                r["eagain"] == FORKS_REQUESTED - (PIDS_SMALL - 1))
        R.check("b1: no other fork errors", [], r["other_errnos"], not r["other_errnos"])
        R.check("b1: lease pids.current", PIDS_SMALL, s["pids.current"], s["pids.current"] == PIDS_SMALL)
        pk = s["pids.peak"]
        R.check("b1: lease pids.peak <= pids.max (if the kernel exposes it)", "<= %d" % PIDS_SMALL, pk,
                pk is None or pk <= PIDS_SMALL)
    finally:
        R.raw["b1_cleanup"] = m.close()

    # (b2) joint pids: run pids.max 8, two leases with pids.max 8 each. A holds 1+3 pids; B asks for 12 children.
    m = Meter("r%d-h2b2" % rep, Limits(pids_max=PIDS_SMALL))
    try:
        m.create_lease("a", Limits(pids_max=PIDS_SMALL))
        m.create_lease("b", Limits(pids_max=PIDS_SMALL))
        R.raw["b2_settings"] = m.settings()
        with ctx.log("h2b2-a") as la:
            pa = m.launch("a", UID_A, ctx.wl("tree", "--children", HOLDER_CHILDREN, "--grandchildren", 0),
                          stderr=la)
        read_ready(pa)
        with ctx.log("h2b2-b") as lb:
            pb = m.launch("b", UID_B, ctx.wl("forks", "--n", FORKS_REQUESTED), stderr=lb)
        r = read_ready(pb)
        sa, sb, sr = strip_procs(m.stats("a")), strip_procs(m.stats("b")), strip_procs(m.stats())
        R.raw["b2"] = {"ready_b": r, "lease_a": sa, "lease_b": sb, "run": sr}
        free = PIDS_SMALL - (1 + HOLDER_CHILDREN) - 1
        R.check("b2: lease A holds 1+%d pids" % HOLDER_CHILDREN, 1 + HOLDER_CHILDREN, sa["pids.current"],
                sa["pids.current"] == 1 + HOLDER_CHILDREN)
        R.check("b2: lease B forks succeeded (bounded by the run, not by B's own limit)", free, r["ok"],
                r["ok"] == free)
        R.check("b2: lease B forks refused with EAGAIN", FORKS_REQUESTED - free, r["eagain"],
                r["eagain"] == FORKS_REQUESTED - free)
        R.check("b2: no other fork errors", [], r["other_errnos"], not r["other_errnos"])
        R.check("b2: run pids.current == run pids.max", PIDS_SMALL, sr["pids.current"],
                sr["pids.current"] == PIDS_SMALL)
        pk = sr["pids.peak"]
        R.check("b2: run pids.peak <= run pids.max (if exposed)", "<= %d" % PIDS_SMALL, pk,
                pk is None or pk <= PIDS_SMALL)
    finally:
        R.raw["b2_cleanup"] = m.close()


def _two_trees(ctx, m, tag, b_cpu_children=0):
    with ctx.log(tag + "-a") as la, ctx.log(tag + "-b") as lb:
        pa = m.launch("a", UID_A, ctx.wl("tree", *TREE_ARGS, "--cpu-children", 1, "--cpu-seconds", 2.0, "--daemon"),
                      stderr=la)
        pb = m.launch("b", UID_B, ctx.wl("tree", *TREE_ARGS, "--cpu-children", b_cpu_children, "--cpu-seconds",
                                         3.0, "--daemon"), stderr=lb)
    return read_ready(pa), read_ready(pb)


def _refused(fn):
    try:
        fn()
    except Refused as e:
        return "refused: %s" % e
    return "ACCEPTED"


def h3(ctx, rep, R):
    m = Meter("r%d-h3" % rep, Limits(pids_max=64))
    try:
        m.create_lease("a", Limits(pids_max=32))
        m.create_lease("b", Limits(pids_max=32))
        R.raw["settings"] = m.settings()
        ra, rb = _two_trees(ctx, m, "h3")
        before_a, before_b = set(m.lease_procs("a")), set(m.lease_procs("b"))
        R.check("precondition: lease A holds the full tree", TREE_N, len(before_a), before_a == tree_pids(ra))
        R.check("precondition: lease B holds the full tree", TREE_N, len(before_b), before_b == tree_pids(rb))
        t0 = m.revoke("a")
        g = wait_gone({UID_A}, t0, KILL_BOUND, REAP_BOUND, extra=lambda: not m.lease_procs("a"), reap=m.reap)
        R.raw["revoke"] = g
        R.check("zero live uid-%d processes and empty lease cgroup within %.1fs of revoke" % (UID_A, KILL_BOUND),
                "<= %.1f s" % KILL_BOUND, g["live_zero_s"],
                g["live_zero_s"] is not None and g["live_zero_s"] <= KILL_BOUND)
        R.check("no uid-%d /proc entry at all (zombies included) within %.1fs" % (UID_A, REAP_BOUND),
                "<= %.1f s" % REAP_BOUND, g["all_zero_s"], g["all_zero_s"] is not None and g["all_zero_s"] <= REAP_BOUND)
        after_b, lv_b = set(m.lease_procs("b")), live(proc_scan({UID_B}))
        R.check("lease B untouched (same pids, all live)", {"same": True, "live_eq": True},
                {"same": after_b == before_b, "live_eq": lv_b == before_b}, after_b == before_b == lv_b)
        with ctx.log("h3-relaunch") as lf:
            res = _refused(lambda: m.launch("a", UID_A, ctx.wl("tree", "--children", 1, "--grandchildren", 0),
                                            stderr=lf))
        time.sleep(REFUSAL_SETTLE)
        late = proc_scan({UID_A})
        R.check("later launch into revoked lease refused", "refused", res, res.startswith("refused"))
        R.check("no uid-%d process after the refused launch" % UID_A, 0, len(late), not late)
        R.raw["lease_a_after"] = strip_procs(m.stats("a"))
    finally:
        R.raw["cleanup"] = m.close()


def h4(ctx, rep, R):
    m = Meter("r%d-h4" % rep, Limits(pids_max=64))
    try:
        m.create_lease("a", Limits(pids_max=32))
        m.create_lease("b", Limits(pids_max=32))
        R.raw["settings"] = m.settings()
        ra, rb = _two_trees(ctx, m, "h4", b_cpu_children=2)
        n0 = len(live(proc_scan({UID_A, UID_B})))
        R.check("precondition: both trees live", 2 * TREE_N, n0, n0 == 2 * TREE_N)
        h = m.halt(FREEZE_BOUND)
        g = wait_gone({UID_A, UID_B}, h["t0"], KILL_BOUND, REAP_BOUND, reap=m.reap,
                      extra=lambda: not meter.procs(m.path / "lease-a") and not meter.procs(m.path / "lease-b"))
        R.raw.update(halt=h, gone=g, run_after=strip_procs(m.stats()))
        R.check("run frozen (cgroup.events frozen 1) within %.1fs before kill" % FREEZE_BOUND, True,
                {"frozen": h["frozen"], "s": h["freeze_latency_s"]}, h["frozen"])
        R.check("zero live workload-UID processes within %.1fs of HALT" % KILL_BOUND, "<= %.1f s" % KILL_BOUND,
                g["live_zero_s"], g["live_zero_s"] is not None and g["live_zero_s"] <= KILL_BOUND)
        R.check("no workload-UID /proc entry at all within %.1fs" % REAP_BOUND, "<= %.1f s" % REAP_BOUND,
                g["all_zero_s"], g["all_zero_s"] is not None and g["all_zero_s"] <= REAP_BOUND)
        R.check("run cgroup unpopulated after HALT", 0, R.raw["run_after"]["populated"],
                R.raw["run_after"]["populated"] == 0)
        with ctx.log("h4-relaunch") as lf:
            res = [_refused(lambda: m.launch("a", UID_A, ctx.wl("tree", "--children", 1, "--grandchildren", 0),
                                             stderr=lf)),
                   _refused(lambda: m.launch("b", UID_B, ctx.wl("cpu", "--seconds", 1.0), stderr=lf)),
                   _refused(lambda: m.create_lease("c"))]
        time.sleep(REFUSAL_SETTLE)
        late = proc_scan({UID_A, UID_B})
        R.check("launches into A, B and lease creation refused after HALT", ["refused"] * 3, res,
                all(x.startswith("refused") for x in res))
        R.check("no workload-UID process after the refused launches", 0, len(late), not late)
    finally:
        R.raw["cleanup"] = m.close()


def h5(ctx, rep, R):
    m = Meter("r%d-h5" % rep, Limits(pids_max=64))
    pu = None
    try:
        m.create_lease("l", Limits(pids_max=32))
        R.raw["settings"] = m.settings()
        # Unplaced: same tree, all sleeping (it is not under any cap while it runs), credential drop only.
        with ctx.log("h5-unplaced") as lf:
            pu = launch_unplaced(ctx, UID_UNPLACED, ctx.wl("tree", *TREE_ARGS, "--daemon"), stderr=lf)
        ru = read_ready(pu)
        lv_u = live(proc_scan({UID_UNPLACED}))
        sl, sr = m.stats("l"), m.stats()
        cgs = sorted({e["cgroup"] for e in proc_scan({UID_UNPLACED})})
        R.raw["unplaced"] = {"ready": ru, "cgroups": cgs, "lease": strip_procs(sl), "run": strip_procs(sr)}
        R.check("unplaced tree is running (independent /proc scan)", TREE_N, len(lv_u),
                len(lv_u) == TREE_N and lv_u == tree_pids(ru))
        R.check("lease accounting sees none of it (cgroup.procs n, pids.current)", [0, 0],
                [len(set(sl["procs"]) & lv_u), sl["pids.current"]],
                not (set(sl["procs"]) & lv_u) and sl["pids.current"] == 0)
        R.check("run accounting sees none of it (pids.current)", 0, sr["pids.current"], sr["pids.current"] == 0)
        outside = all(not (c or "").startswith("0::/sc28-test") for c in cgs)
        R.check("unplaced processes are outside /sc28-test", True, cgs, outside)
        # Placed: same tree through the controller.
        with ctx.log("h5-placed") as lf:
            pp = m.launch("l", UID_A, ctx.wl("tree", *TREE_ARGS, "--daemon"), stderr=lf)
        rp = read_ready(pp)
        cg, lv_a = set(m.lease_procs("l")), live(proc_scan({UID_A}))
        R.raw["placed"] = {"ready": rp, "lease": strip_procs(m.stats("l"))}
        R.check("placed tree fully visible to the lease (cgroup.procs == /proc scan)", TREE_N, len(cg),
                cg == lv_a == tree_pids(rp))
        # Cleanup of the unplaced tree by UID.
        k = kill_uid(UID_UNPLACED, reap=lambda: pu.poll())
        pu.poll()
        g = wait_gone({UID_UNPLACED}, time.monotonic(), REAP_BOUND, REAP_BOUND, reap=lambda: pu.poll())
        R.raw["unplaced_cleanup"] = {"kill_uid": k, "gone": g}
        R.check("unplaced tree removed by kill-by-UID (no /proc entry left)", 0, len(g["left"]),
                k["ok"] and g["all_zero_s"] is not None)
    finally:
        if pu is not None:
            kill_uid(UID_UNPLACED, reap=lambda: pu.poll())
            try:
                pu.wait(timeout=2)
            except subprocess.TimeoutExpired:
                pass
            if pu.stdout:
                pu.stdout.close()
        R.raw["cleanup"] = m.close()


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
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    return {
        "prereg_id": PREREG_ID,
        "kind": args.kind,
        "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"),
        "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "uname_r": platform.release(),
        "uname_a": " ".join(platform.uname()),
        "python": sys.version,
        "python_executable": sys.executable,
        "nproc": os.cpu_count(),
        "cgroup_root_subtree_control": meter._r(meter.CG_ROOT / "cgroup.subtree_control").strip(),
        "controller_cgroup": open("/proc/self/cgroup").read().strip(),
        "uids": {"A": UID_A, "B": UID_B, "unplaced": UID_UNPLACED, "reserved_range": [ALL_UIDS[0], ALL_UIDS[-1]]},
        "constants": {k: globals()[k] for k in ("TREE_N", "LIFETIME", "PARENT_CPU", "CPU_TOL", "CPU_WINDOW",
                                                 "CPU_WARMUP", "CPU_SECONDS", "KILL_BOUND", "REAP_BOUND",
                                                 "FREEZE_BOUND", "REFUSAL_SETTLE", "PIDS_SMALL", "FORKS_REQUESTED",
                                                 "HOLDER_CHILDREN", "WALL_LIMIT")},
    }


def preflight():
    problems = []
    if os.geteuid() != 0:
        problems.append("must run as root")
    if not (meter.CG_ROOT / "cgroup.controllers").exists():
        problems.append("cgroup v2 not mounted at /sys/fs/cgroup")
    else:
        ctl = meter._r(meter.CG_ROOT / "cgroup.subtree_control").split()
        problems += ["controller %s not enabled at root" % c for c in meter.CONTROLLERS if c not in ctl]
    if meter.TOP.exists():
        problems.append("%s already exists (stale run? use --cleanup-stale)" % meter.TOP)
    stale = proc_scan(set(ALL_UIDS))
    if stale:
        problems.append("processes already running under reserved UIDs: %s" % [e["pid"] for e in stale])
    return problems


def cleanup_all(popens=()):
    rep = {"kill_uid": {}, "top": None}
    for u in ALL_UIDS:
        if proc_scan({u}):
            rep["kill_uid"][u] = kill_uid(u)
    if meter.TOP.exists():
        rep["top"] = meter.destroy(meter.TOP)
    rep["left_procs"] = proc_scan(set(ALL_UIDS))
    rep["top_exists"] = meter.TOP.exists()
    return rep


def summary_md(m, verdicts, results):
    lines = ["# SC-28 cgroup meter run (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- kernel: `%s`, python `%s`" % (m["uname_r"], m["python"].split()[0]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | reps passed | verdict |", "|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %d/%d | %s |" % (h, v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"])))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-28 cgroup v2 meter check (root).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    ap.add_argument("--cleanup-stale", action="store_true", help="only remove a stale sc28-test and exit")
    args = ap.parse_args()
    if args.cleanup_stale:
        print(json.dumps(cleanup_all(), indent=1, default=str))
        return 0
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
    out.mkdir()
    (out / "logs").mkdir()
    m = meta(args)
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, cleanup, infra, aborted = [], None, None, None
    problems = preflight()
    if args.kind == "evidence" and m["git_status_harness_and_prereg"]:
        problems.append("evidence run needs committed, unmodified harness and prereg files")
    ctx = None
    if problems:
        infra = problems
    else:
        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            m["top_settings"] = meter.ensure_top()
            ctx = Ctx()
            m["sha256"]["<workdir>/code/workloads.py"] = sha(ctx.wl_path)
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
                    # Stop rule: nothing of ours may survive a hypothesis.
                    left = proc_scan(set(ALL_UIDS))
                    kids = [p.name for p in meter.TOP.iterdir() if p.is_dir()]
                    R.raw["after"] = {"left_procs": left, "top_children": kids}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL",
                                                      R.raw["elapsed_s"]), flush=True)
                    if left or kids:
                        aborted = "residue after %s rep %d: procs %s cgroups %s" % (h, rep, left, kids)
                        raise RuntimeError(aborted)
        except Exception:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            cleanup = cleanup_all()
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                shutil.rmtree(str(ctx.work), ignore_errors=True)
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        complete = len(rs) == args.reps
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok,
                  "verdict": "NOT-RUN" if infra else "PASS" if complete and n_ok == args.reps else "FAIL"}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": (not meter.TOP.exists()) if cleanup is None else (
                    not cleanup["left_procs"] and not cleanup["top_exists"]),
                "per_hypothesis": per}
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
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if uid and gid:
        for root, dirs, files in os.walk(str(out)):
            for n in [root] + [os.path.join(root, f) for f in dirs + files]:
                os.chown(n, int(uid), int(gid))
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra},
                     indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
