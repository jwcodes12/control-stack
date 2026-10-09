#!/usr/bin/env python3
"""SC-28 trusted job controller ("meter"), cgroup v2, root only.

A run is one parent cgroup /sys/fs/cgroup/sc28-test/<run> with a global cap (cpu.max, pids.max, memory.max). Each
lease is one child cgroup <run>/lease-<name> with its own limits. Limits are written, and read back, before any
process can enter a cgroup.

Launch = placement before exec. The controller forks; the child, still root, writes its own pid into the lease's
cgroup.procs, checks /proc/self/cgroup, drops to the workload's numeric UID (setgroups/setgid/setuid) and only then
execs the workload. A placement or credential failure aborts the launch before exec (fail closed).

Revoke = mark the lease revoked (later launches into it are refused), then write 1 to its cgroup.kill.
HALT = mark the run halted (later launches and lease creation are refused), write 1 to the run's cgroup.freeze,
wait (bounded) for cgroup.events "frozen 1", then write 1 to the run's cgroup.kill.

Host-safety bounds are enforced here, not only by the caller: cgroups only under /sys/fs/cgroup/sc28-test,
pids.max <= 64, memory.max <= 128 MiB, cpu.max quota <= 50000 per 100000 period, workload UIDs only in
23700..23709. Python 3.9 compatible.
"""
import os
import subprocess
import time
from pathlib import Path

CG_ROOT = Path("/sys/fs/cgroup")
TOP = CG_ROOT / "sc28-test"
CONTROLLERS = ("cpu", "memory", "pids")
MAX_PIDS = 64
MAX_MEM = 128 * 1024 * 1024
CPU_PERIOD = 100000
MAX_QUOTA = 50000
WORKLOAD_UIDS = range(23700, 23710)
ENV = {"PATH": "/usr/sbin:/usr/bin:/sbin:/bin", "LANG": "C.UTF-8"}


class Refused(Exception):
    """The controller refused an operation (revoked lease, HALTed run, unknown lease)."""


def _w(path, val):
    with open(str(path), "w") as f:
        f.write(val)


def _r(path):
    with open(str(path)) as f:
        return f.read()


def _inside_top(path):
    path = Path(path)
    return path == TOP or TOP in path.parents


def cgpath(path):
    """The cgroup path as it appears in /proc/<pid>/cgroup ("/sc28-test/...")."""
    return "/" + str(Path(path).relative_to(CG_ROOT))


class Limits:
    def __init__(self, cpu_max="50000 100000", pids_max=MAX_PIDS, memory_max=MAX_MEM):
        q, per = cpu_max.split()
        if int(per) != CPU_PERIOD or not 0 < int(q) <= MAX_QUOTA:
            raise ValueError("cpu.max outside host-safety bound: %r" % cpu_max)
        if not 1 <= int(pids_max) <= MAX_PIDS:
            raise ValueError("pids.max outside host-safety bound: %r" % pids_max)
        if not 0 < int(memory_max) <= MAX_MEM:
            raise ValueError("memory.max outside host-safety bound: %r" % memory_max)
        self.cpu_max, self.pids_max, self.memory_max = cpu_max, int(pids_max), int(memory_max)

    def apply(self, path):
        _w(path / "cpu.max", self.cpu_max)
        _w(path / "pids.max", str(self.pids_max))
        _w(path / "memory.max", str(self.memory_max))
        got = settings(path)
        want = {"cpu.max": self.cpu_max, "pids.max": str(self.pids_max), "memory.max": str(self.memory_max)}
        for k, v in want.items():
            if got[k] != v:
                raise RuntimeError("limit read-back mismatch on %s %s: want %r got %r" % (path, k, v, got[k]))
        return got


def settings(path):
    out = {}
    for k in ("cpu.max", "pids.max", "memory.max", "cgroup.subtree_control", "cgroup.controllers", "cgroup.type"):
        try:
            out[k] = _r(path / k).strip()
        except FileNotFoundError:
            out[k] = None
    return out


def make_cgroup(path, limits, delegate):
    """mkdir (must not exist) -> write + verify limits -> optionally enable controllers for children.
    The cgroup has no processes at any point of this function."""
    path = Path(path)
    if not _inside_top(path):
        raise ValueError("refusing to create a cgroup outside %s: %s" % (TOP, path))
    path.mkdir()
    procs = _r(path / "cgroup.procs").split()
    if procs:
        raise RuntimeError("fresh cgroup unexpectedly populated: %s" % path)
    limits.apply(path)
    if delegate:
        _w(path / "cgroup.subtree_control", " ".join("+" + c for c in CONTROLLERS))
    return settings(path)


def procs(path):
    return [int(x) for x in _r(Path(path) / "cgroup.procs").split()]


def _kv(text):
    out = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 2:
            try:
                out[parts[0]] = int(parts[1])
            except ValueError:
                out[parts[0]] = parts[1]
    return out


def read_stats(path):
    path = Path(path)
    s = {"t": time.monotonic()}
    cpu = _kv(_r(path / "cpu.stat"))
    for k in ("usage_usec", "user_usec", "system_usec", "nr_periods", "nr_throttled", "throttled_usec"):
        s["cpu." + k] = cpu.get(k)
    s["pids.current"] = int(_r(path / "pids.current"))
    for k in ("pids.peak", "memory.peak"):
        try:
            s[k] = int(_r(path / k))
        except (FileNotFoundError, ValueError):
            s[k] = None
    for k in ("pids.events", "pids.events.local", "memory.events"):
        try:
            s[k] = _kv(_r(path / k))
        except FileNotFoundError:
            s[k] = None
    s["memory.current"] = int(_r(path / "memory.current"))
    ev = _kv(_r(path / "cgroup.events"))
    s["populated"], s["frozen"] = ev.get("populated"), ev.get("frozen")
    s["procs"] = procs(path)
    return s


def cpu_usage(path):
    """Fast path for windowed CPU measurement: (monotonic time, usage_usec, nr_throttled)."""
    t = time.monotonic()
    d = _kv(_r(Path(path) / "cpu.stat"))
    return t, d["usage_usec"], d["nr_throttled"]


def _subtree(path):
    """All cgroup directories under path, deepest first, path last."""
    out = []
    for child in sorted(p for p in Path(path).iterdir() if p.is_dir()):
        out.extend(_subtree(child))
    out.append(Path(path))
    return out


def destroy(path, timeout=5.0):
    """cgroup.kill -> wait until every cgroup.procs in the subtree is empty -> rmdir children, then the parent."""
    path = Path(path)
    if not _inside_top(path):
        raise ValueError("refusing to destroy outside %s: %s" % (TOP, path))
    if not path.exists():
        return {"existed": False}
    t0 = time.monotonic()
    try:
        _w(path / "cgroup.freeze", "0")
    except OSError:
        pass
    _w(path / "cgroup.kill", "1")
    nodes = _subtree(path)
    while True:
        left = {cgpath(n): procs(n) for n in nodes if procs(n)}
        if not left:
            break
        if time.monotonic() - t0 > timeout:
            raise RuntimeError("cgroup subtree still populated after %.1fs: %s" % (timeout, left))
        time.sleep(0.01)
    t_empty = time.monotonic() - t0
    removed = []
    for n in nodes:
        for attempt in range(200):
            try:
                n.rmdir()
                removed.append(cgpath(n))
                break
            except OSError as e:
                if attempt == 199:
                    raise RuntimeError("rmdir %s failed: %s" % (n, e))
                time.sleep(0.01)
    return {"existed": True, "empty_after_s": round(t_empty, 4), "removed": removed}


def ensure_top():
    """Create /sys/fs/cgroup/sc28-test (must not already exist) with the host-safety caps."""
    root_ctl = _r(CG_ROOT / "cgroup.subtree_control").split()
    missing = [c for c in CONTROLLERS if c not in root_ctl]
    if missing:
        raise RuntimeError("controllers not enabled at the cgroup root: %s" % missing)
    return make_cgroup(TOP, Limits(), delegate=True)


def _launcher(procs_file, expect_cg, uid):
    """Runs in the forked child, as root, before exec: place itself, verify placement, then drop privileges."""
    def child():
        fd = os.open(procs_file, os.O_WRONLY)
        try:
            os.write(fd, str(os.getpid()).encode())
        finally:
            os.close(fd)
        with open("/proc/self/cgroup") as fh:
            got = fh.read().strip()
        if got != "0::" + expect_cg:
            raise RuntimeError("placement check failed: %r" % got)
        os.setgroups([])
        os.setgid(uid)
        os.setuid(uid)
        if (os.getuid(), os.geteuid(), os.getgid(), os.getegid()) != (uid, uid, uid, uid):
            raise RuntimeError("credential drop failed")
        os.umask(0o077)
    return child


class Lease:
    def __init__(self, name, path, limits_readback):
        self.name, self.path, self.settings = name, path, limits_readback
        self.revoked = False
        self.revoked_at = None
        self.launches = []


class Meter:
    def __init__(self, run_name, limits=None):
        self.path = TOP / run_name
        self.limits = limits or Limits()
        self.run_settings = make_cgroup(self.path, self.limits, delegate=True)
        self.leases = {}
        self.halted = False
        self.popens = []
        self.events = []

    def _ev(self, kind, **kw):
        kw.update(kind=kind, t=time.monotonic())
        self.events.append(kw)

    def create_lease(self, name, limits=None):
        if self.halted:
            self._ev("create_lease_refused", lease=name, reason="halted")
            raise Refused("run is HALTed")
        if name in self.leases:
            raise Refused("lease exists: %s" % name)
        path = self.path / ("lease-" + name)
        rb = make_cgroup(path, limits or Limits(pids_max=32), delegate=False)
        self.leases[name] = Lease(name, path, rb)
        self._ev("create_lease", lease=name, settings=rb)
        return self.leases[name]

    def launch(self, lease, uid, argv, stdout=subprocess.PIPE, stderr=None):
        if self.halted:
            self._ev("launch_refused", lease=lease, reason="halted")
            raise Refused("run is HALTed")
        L = self.leases.get(lease)
        if L is None:
            self._ev("launch_refused", lease=lease, reason="unknown")
            raise Refused("unknown lease %s" % lease)
        if L.revoked:
            self._ev("launch_refused", lease=lease, reason="revoked")
            raise Refused("lease %s is revoked" % lease)
        if uid not in WORKLOAD_UIDS:
            raise ValueError("uid outside the reserved workload range: %d" % uid)
        p = subprocess.Popen(argv, preexec_fn=_launcher(str(L.path / "cgroup.procs"), cgpath(L.path), uid),
                             stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr, cwd="/", env=dict(ENV),
                             close_fds=True)
        self.popens.append(p)
        L.launches.append(p.pid)
        self._ev("launch", lease=lease, uid=uid, pid=p.pid)
        return p

    def revoke(self, lease):
        L = self.leases[lease]
        L.revoked = True  # refuse first, then kill
        t0 = time.monotonic()
        L.revoked_at = t0
        _w(L.path / "cgroup.kill", "1")
        self._ev("revoke", lease=lease)
        return t0

    def halt(self, freeze_timeout=0.5):
        self.halted = True  # refuse first
        t0 = time.monotonic()
        _w(self.path / "cgroup.freeze", "1")
        frozen = False
        while time.monotonic() - t0 < freeze_timeout:
            if _kv(_r(self.path / "cgroup.events")).get("frozen") == 1:
                frozen = True
                break
            time.sleep(0.002)
        t_frozen = time.monotonic()
        _w(self.path / "cgroup.kill", "1")
        t_kill = time.monotonic()
        self._ev("halt", frozen=frozen)
        return {"t0": t0, "frozen": frozen, "freeze_latency_s": round(t_frozen - t0, 4),
                "kill_written_s": round(t_kill - t0, 4)}

    def lease_procs(self, lease):
        return procs(self.leases[lease].path)

    def stats(self, lease=None):
        return read_stats(self.leases[lease].path if lease else self.path)

    def settings(self):
        return {"run": settings(self.path),
                "leases": {n: settings(L.path) for n, L in self.leases.items() if L.path.exists()}}

    def reap(self):
        for p in self.popens:
            p.poll()

    def close(self):
        rep = destroy(self.path)
        for p in self.popens:
            try:
                p.wait(timeout=2)
            except subprocess.TimeoutExpired:
                pass
            if p.stdout:
                p.stdout.close()
        return rep
