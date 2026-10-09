#!/usr/bin/env python3
"""Minimal trusted cgroup-v2 controller shared (identical copies) by the SC-12 and SC-14 harnesses. Root only.

Host-safety bounds are enforced HERE, not only by callers:
  * cgroups only under /sys/fs/cgroup/<top> where <top> is "sc12-test" or "sc14-test";
  * limits are written and read back BEFORE any process enters a cgroup: pids.max <= 64, memory.max <= 128 MiB,
    cpu.max quota <= 50000 per 100000 period;
  * workloads run only as numeric UIDs in the caller's reserved range (within 23901..23909); no accounts are created;
  * a launch places the forked child into its cgroup and verifies /proc/self/cgroup BEFORE dropping privileges and
    exec (fail closed); `launch_unplaced` exists only for negative controls and still drops to a reserved UID.
Independent observation (`proc_scan`) reads only /proc. Python 3.9 compatible.
"""
import os
import signal
import subprocess
import time
from pathlib import Path

CG_ROOT = Path("/sys/fs/cgroup")
ALLOWED_TOPS = ("sc12-test", "sc14-test")
CONTROLLERS = ("cpu", "memory", "pids")
MAX_PIDS = 64
MAX_MEM = 128 * 1024 * 1024
PERIOD = 100000
MAX_QUOTA = 50000
ALL_RESERVED = range(23901, 23910)
ENV = {"PATH": "/usr/sbin:/usr/bin:/sbin:/bin", "LANG": "C.UTF-8"}


def w(path, val):
    with open(str(path), "w") as f:
        f.write(val)


def r(path):
    with open(str(path)) as f:
        return f.read()


def kv(text):
    out = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 2:
            try:
                out[parts[0]] = int(parts[1])
            except ValueError:
                out[parts[0]] = parts[1]
    return out


def procs(path):
    return [int(x) for x in r(Path(path) / "cgroup.procs").split()]


class Cg:
    def __init__(self, top, uids):
        if top not in ALLOWED_TOPS:
            raise ValueError("top cgroup must be one of %s" % (ALLOWED_TOPS,))
        if not set(uids) <= set(ALL_RESERVED):
            raise ValueError("uids outside 23901..23909")
        self.top, self.uids = CG_ROOT / top, tuple(uids)

    def inside(self, path):
        path = Path(path)
        return path == self.top or self.top in path.parents

    def cgpath(self, path):
        return "/" + str(Path(path).relative_to(CG_ROOT))

    def limits(self, path, cpu_max="50000 100000", pids_max=MAX_PIDS, memory_max=MAX_MEM):
        q, per = cpu_max.split()
        if int(per) != PERIOD or not 0 < int(q) <= MAX_QUOTA:
            raise ValueError("cpu.max outside host bound: %r" % cpu_max)
        if not 1 <= int(pids_max) <= MAX_PIDS or not 0 < int(memory_max) <= MAX_MEM:
            raise ValueError("pids/memory outside host bound")
        w(path / "cpu.max", cpu_max)
        w(path / "pids.max", str(int(pids_max)))
        w(path / "memory.max", str(int(memory_max)))
        got = {k: r(path / k).strip() for k in ("cpu.max", "pids.max", "memory.max")}
        want = {"cpu.max": cpu_max, "pids.max": str(int(pids_max)), "memory.max": str(int(memory_max))}
        if got != want:
            raise RuntimeError("limit read-back mismatch: want %r got %r" % (want, got))
        return got

    def ensure_top(self):
        ctl = r(CG_ROOT / "cgroup.subtree_control").split()
        missing = [c for c in CONTROLLERS if c not in ctl]
        if missing:
            raise RuntimeError("controllers not enabled at the cgroup root: %s" % missing)
        self.top.mkdir()  # must not exist
        self.limits(self.top)
        w(self.top / "cgroup.subtree_control", " ".join("+" + c for c in CONTROLLERS))

    def make(self, name, **lim):
        """create an empty child cgroup of the top, write + verify its limits; no process is in it yet"""
        path = self.top / name
        if not self.inside(path) or path == self.top:
            raise ValueError("bad cgroup name")
        path.mkdir()
        if procs(path):
            raise RuntimeError("fresh cgroup unexpectedly populated")
        return path, self.limits(path, **lim)

    def _launcher(self, path, uid):
        procs_file, expect = str(Path(path) / "cgroup.procs"), "0::" + self.cgpath(path)

        def child():
            fd = os.open(procs_file, os.O_WRONLY)
            try:
                os.write(fd, str(os.getpid()).encode())
            finally:
                os.close(fd)
            with open("/proc/self/cgroup") as fh:
                if fh.read().strip() != expect:
                    raise RuntimeError("placement check failed")
            self._drop(uid)
        return child

    def _drop(self, uid):
        if uid not in self.uids:
            raise RuntimeError("uid outside reserved range")
        os.setgroups([])
        os.setgid(uid)
        os.setuid(uid)
        if (os.getuid(), os.geteuid(), os.getgid(), os.getegid()) != (uid, uid, uid, uid):
            raise RuntimeError("credential drop failed")
        os.umask(0o022)

    def launch(self, path, uid, argv, stdout=subprocess.PIPE, stderr=None, cwd="/"):
        if uid not in self.uids or not self.inside(path):
            raise ValueError("launch outside reserved uid range or cgroup tree")
        return subprocess.Popen(argv, preexec_fn=self._launcher(path, uid), stdin=subprocess.DEVNULL, stdout=stdout,
                                stderr=stderr, cwd=cwd, env=dict(ENV), close_fds=True)

    def launch_unplaced(self, uid, argv, stdout=subprocess.PIPE, stderr=None, cwd="/"):
        """negative controls only: same credential drop, NO cgroup placement"""
        if uid not in self.uids:
            raise ValueError("uid outside reserved range")
        return subprocess.Popen(argv, preexec_fn=lambda: self._drop(uid), stdin=subprocess.DEVNULL, stdout=stdout,
                                stderr=stderr, cwd=cwd, env=dict(ENV), close_fds=True)

    def kill(self, path):
        if not self.inside(path):
            raise ValueError("refusing to kill outside the top cgroup")
        w(Path(path) / "cgroup.kill", "1")

    def destroy(self, path, timeout=5.0):
        path = Path(path)
        if not self.inside(path) or not path.exists():
            return {"existed": path.exists()}
        nodes = sorted((p for p in path.rglob("*") if p.is_dir()), key=lambda p: -len(p.parts)) + [path]
        t0 = time.monotonic()
        w(path / "cgroup.kill", "1")
        while any(procs(n) for n in nodes):
            if time.monotonic() - t0 > timeout:
                raise RuntimeError("cgroup still populated after kill: %s" % path)
            time.sleep(0.01)
        for n in nodes:
            for attempt in range(200):
                try:
                    n.rmdir()
                    break
                except OSError:
                    if attempt == 199:
                        raise
                    time.sleep(0.01)
        return {"existed": True, "empty_after_s": round(time.monotonic() - t0, 4)}


# ---------------------------------------------------------------- independent observation (reads only /proc)
def proc_scan(uids):
    out = []
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/status" % d) as fh:
                status = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        uid = state = None
        for line in status.splitlines():
            if line.startswith("Uid:"):
                uid = int(line.split()[1])
            elif line.startswith("State:"):
                state = line.split()[1]
        if uid not in uids:
            continue
        cg = None
        try:
            with open("/proc/%s/cgroup" % d) as fh:
                cg = fh.read().strip()
        except (FileNotFoundError, ProcessLookupError):
            pass
        out.append({"pid": int(d), "uid": uid, "state": state, "cgroup": cg})
    return out


def live(entries):
    return {e["pid"] for e in entries if e["state"] not in ("Z", "X")}


def kill_uid(uid, reserved, timeout=5.0, reap=None):
    """SIGKILL (pidfd, race-free) every live process of a reserved uid until 3 consecutive empty scans"""
    if uid not in reserved:
        raise ValueError("kill_uid refuses uid %d" % uid)
    t0, quiet = time.monotonic(), 0
    while time.monotonic() - t0 < timeout:
        if reap:
            reap()
        pids = live(proc_scan({uid}))
        if not pids:
            quiet += 1
            if quiet >= 3:
                return {"ok": True, "s": round(time.monotonic() - t0, 4)}
            time.sleep(0.01)
            continue
        quiet = 0
        for pid in pids:
            try:
                fd = os.pidfd_open(pid)
            except OSError:
                continue
            try:
                with open("/proc/%d/status" % pid) as fh:
                    if any(l.startswith("Uid:") and int(l.split()[1]) == uid for l in fh):
                        signal.pidfd_send_signal(fd, signal.SIGKILL)
            except (FileNotFoundError, ProcessLookupError, OSError):
                pass
            finally:
                os.close(fd)
        time.sleep(0.005)
    return {"ok": False, "left": sorted(live(proc_scan({uid})))}


def wait_gone(uids, t0, bound, reap=None):
    """poll /proc until no live process of uids, then until no entry at all; latencies from t0"""
    t_live = t_all = None
    while True:
        if reap:
            reap()
        ents = proc_scan(set(uids))
        now = time.monotonic()
        if t_live is None and not live(ents):
            t_live = now - t0
        if t_live is not None and not ents:
            t_all = now - t0
            break
        if now - t0 > bound + 1.0:
            break
        time.sleep(0.002)
    return {"live_zero_s": None if t_live is None else round(t_live, 4),
            "all_zero_s": None if t_all is None else round(t_all, 4),
            "left": [] if t_all is not None else proc_scan(set(uids))}
