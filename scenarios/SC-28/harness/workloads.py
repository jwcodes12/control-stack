#!/usr/bin/env python3
"""SC-28 benign workloads (run as an unprivileged numeric UID, launched by meter.py or, for the H5 control, by
run_sc28.py without cgroup placement).

Every workload here is ordinary and bounded:
  * every process exits by itself at its --lifetime deadline (default 30 s);
  * no process ignores or blocks signals, changes its cgroup, retries a failed fork, or does anything else evasive;
  * CPU work is a fixed wall-clock budget of integer arithmetic (--cpu-seconds / --seconds);
  * the process tree is small: one parent, <= 8 children, <= 2 grandchildren per child, and optionally one
    conventional daemon-style child started with start_new_session=True (as an ordinary service would be).

Each workload prints exactly one line "READY <json>" on stdout once it is fully started, then sleeps until its
deadline. Python 3.9 compatible (the root launcher runs the system interpreter).
"""
import argparse
import json
import os
import select
import subprocess
import sys
import time

MAX_CHILDREN = 8
MAX_GRANDCHILDREN = 2
MAX_FORKS = 12
MAX_LIFETIME = 60.0
MAX_CPU_SECONDS = 5.0


def sleep_until(deadline):
    while True:
        rem = deadline - time.monotonic()
        if rem <= 0:
            return
        time.sleep(min(rem, 1.0))


def burn(seconds):
    """Bounded integer arithmetic for `seconds` of wall-clock time."""
    end = time.monotonic() + seconds
    x, rounds = 1, 0
    while True:
        for _ in range(20000):
            x = (x * 1103515245 + 12345) & 0x7FFFFFFF
        rounds += 1
        if time.monotonic() >= end:
            return rounds


def ready(obj):
    sys.stdout.write("READY " + json.dumps(obj, sort_keys=True) + "\n")
    sys.stdout.flush()


def _child(grandchildren, cpu_seconds, deadline, wfd):
    for _ in range(grandchildren):
        pid = os.fork()
        if pid == 0:
            sleep_until(deadline)
            os._exit(0)
        os.write(wfd, ("G %d %d\n" % (os.getpid(), pid)).encode())
    if cpu_seconds > 0:
        burn(cpu_seconds)
    sleep_until(deadline)


def cmd_tree(a):
    if not (0 <= a.children <= MAX_CHILDREN and 0 <= a.grandchildren <= MAX_GRANDCHILDREN):
        sys.exit("tree size out of bounds")
    deadline = time.monotonic() + a.lifetime
    r, w = os.pipe()
    children = []
    for i in range(a.children):
        pid = os.fork()
        if pid == 0:
            code = 0
            try:
                os.close(r)
                _child(a.grandchildren, a.cpu_seconds if i < a.cpu_children else 0.0, deadline, w)
            except BaseException:
                code = 1
            finally:
                os._exit(code)
        children.append(pid)
    daemon = None
    if a.daemon:
        # A conventional service-style child: own session, stdio detached. It reports its pid and session id on the
        # inherited notify pipe and then sleeps until its own deadline.
        p = subprocess.Popen(
            [sys.executable, "-I", "-S", os.path.abspath(__file__), "daemon", "--notify-fd", str(w),
             "--lifetime", str(a.lifetime)],
            start_new_session=True, pass_fds=(w,), close_fds=True,
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        daemon = p.pid
    os.close(w)
    want_g = a.children * a.grandchildren
    grandchildren, daemon_info = [], None
    buf = b""
    limit = time.monotonic() + 10.0
    while (len(grandchildren) < want_g or (a.daemon and daemon_info is None)) and time.monotonic() < limit:
        rl, _, _ = select.select([r], [], [], max(0.0, limit - time.monotonic()))
        if not rl:
            break
        chunk = os.read(r, 4096)
        if not chunk:
            break
        buf += chunk
        while b"\n" in buf:
            line, buf = buf.split(b"\n", 1)
            parts = line.decode().split()
            if parts and parts[0] == "G":
                grandchildren.append(int(parts[2]))
            elif parts and parts[0] == "D":
                daemon_info = {"pid": int(parts[1]), "sid": int(parts[2])}
    ready({"kind": "tree", "parent": os.getpid(), "parent_sid": os.getsid(0), "children": children,
           "grandchildren": sorted(grandchildren), "daemon": daemon,
           "daemon_sid": daemon_info["sid"] if daemon_info else None,
           "daemon_reported_pid": daemon_info["pid"] if daemon_info else None,
           "complete": len(grandchildren) == want_g and (daemon_info is not None) == bool(a.daemon)})
    sleep_until(deadline)


def cmd_daemon(a):
    deadline = time.monotonic() + a.lifetime
    os.write(a.notify_fd, ("D %d %d\n" % (os.getpid(), os.getsid(0))).encode())
    os.close(a.notify_fd)
    sleep_until(deadline)


def cmd_cpu(a):
    if not 0 < a.seconds <= MAX_CPU_SECONDS:
        sys.exit("cpu seconds out of bounds")
    deadline = time.monotonic() + a.lifetime
    ready({"kind": "cpu", "pid": os.getpid(), "seconds": a.seconds})
    burn(a.seconds)
    sleep_until(deadline)


def cmd_forks(a):
    """Ask for n sleeping children with ONE fork attempt each (no retry). Reports how many forks succeeded and how
    many failed with EAGAIN (the pids controller's limit)."""
    if not 0 <= a.n <= MAX_FORKS:
        sys.exit("fork count out of bounds")
    deadline = time.monotonic() + a.lifetime
    ok, eagain, other, pids = 0, 0, [], []
    for _ in range(a.n):
        try:
            pid = os.fork()
        except BlockingIOError:
            eagain += 1
            continue
        except OSError as e:
            other.append(e.errno)
            continue
        if pid == 0:
            sleep_until(deadline)
            os._exit(0)
        ok += 1
        pids.append(pid)
    ready({"kind": "forks", "parent": os.getpid(), "requested": a.n, "ok": ok, "eagain": eagain,
           "other_errnos": other, "children": pids})
    sleep_until(deadline)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("tree")
    t.add_argument("--children", type=int, default=8)
    t.add_argument("--grandchildren", type=int, default=2)
    t.add_argument("--cpu-children", type=int, default=0)
    t.add_argument("--cpu-seconds", type=float, default=2.0)
    t.add_argument("--daemon", action="store_true")
    d = sub.add_parser("daemon")
    d.add_argument("--notify-fd", type=int, required=True)
    c = sub.add_parser("cpu")
    c.add_argument("--seconds", type=float, default=2.0)
    f = sub.add_parser("forks")
    f.add_argument("--n", type=int, default=12)
    for p in (t, d, c, f):
        p.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    if not 0 < a.lifetime <= MAX_LIFETIME:
        sys.exit("lifetime out of bounds")
    if a.cmd == "tree" and a.cpu_seconds > MAX_CPU_SECONDS:
        sys.exit("cpu seconds out of bounds")
    {"tree": cmd_tree, "daemon": cmd_daemon, "cpu": cmd_cpu, "forks": cmd_forks}[a.cmd](a)


if __name__ == "__main__":
    main()
