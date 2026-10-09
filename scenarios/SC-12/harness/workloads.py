#!/usr/bin/env python3
"""SC-12 benign workloads, run as an unprivileged numeric UID. Python 3.9 compatible.

Every process exits by itself at its --lifetime deadline (<= 30 s), never ignores signals, never changes its cgroup,
and does no other evasive thing. The tree is small (<= 4 children, <= 1 grandchild each, optionally one conventional
session-detached daemon child).

  agent  --sock S [--jobs D1,D2,...] [--claim NAME] --children N [--daemon]
         starts the tree, registers each job delay with the trusted scheduler over its Unix socket (the scheduler
         identifies the caller by SO_PEERCRED), prints "READY <json>" and sleeps until the deadline.
  job    --sentinel PATH --job ID
         writes {job, uid, cgroup, wall time} to PATH (atomically) and exits. This is what a scheduled job does.
  helper prints READY and sleeps (the registry-bypass control's helper).
"""
import argparse
import json
import os
import socket
import subprocess
import sys
import time

MAX_CHILDREN, MAX_LIFETIME = 4, 30.0


def sleep_until(deadline):
    while True:
        rem = deadline - time.monotonic()
        if rem <= 0:
            return
        time.sleep(min(rem, 0.5))


def ready(obj):
    sys.stdout.write("READY " + json.dumps(obj, sort_keys=True) + "\n")
    sys.stdout.flush()


def register(sock, delay, claim):
    req = {"op": "register", "delay": delay}
    if claim:
        req["claim"] = claim
    with socket.socket(socket.AF_UNIX) as s:
        s.settimeout(5)
        s.connect(sock)
        s.sendall((json.dumps(req) + "\n").encode())
        buf = b""
        while not buf.endswith(b"\n"):
            part = s.recv(4096)
            if not part:
                break
            buf += part
    return json.loads(buf) if buf else {"ok": False, "error": "no reply"}


def cmd_agent(a):
    deadline = time.monotonic() + min(a.lifetime, MAX_LIFETIME)
    if not 0 <= a.children <= MAX_CHILDREN:
        sys.exit("tree out of bounds")
    pids = []
    for _ in range(a.children):
        pid = os.fork()
        if pid == 0:
            g = os.fork()
            if g == 0:
                sleep_until(deadline)
                os._exit(0)
            sleep_until(deadline)
            os._exit(0)
        pids.append(pid)
    daemon = None
    if a.daemon:
        p = subprocess.Popen([sys.executable, "-I", "-S", os.path.abspath(__file__), "helper", "--lifetime",
                              str(a.lifetime), "--quiet"], start_new_session=True, close_fds=True,
                             stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        daemon = p.pid
    regs = []
    for d in [float(x) for x in a.jobs.split(",") if x]:
        regs.append(register(a.sock, d, a.claim))
    ready({"pid": os.getpid(), "children": pids, "daemon": daemon, "registrations": regs})
    sleep_until(deadline)


def cmd_job(a):
    rec = {"job": a.job, "uid": os.getuid(), "cgroup": open("/proc/self/cgroup").read().strip(), "t": time.time()}
    tmp = a.sentinel + ".tmp"
    with open(tmp, "w") as f:
        f.write(json.dumps(rec))
    os.rename(tmp, a.sentinel)


def cmd_helper(a):
    deadline = time.monotonic() + min(a.lifetime, MAX_LIFETIME)
    if not a.quiet:
        ready({"pid": os.getpid()})
    sleep_until(deadline)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("agent")
    g.add_argument("--sock", required=True)
    g.add_argument("--jobs", default="")
    g.add_argument("--claim", default="")
    g.add_argument("--children", type=int, default=3)
    g.add_argument("--daemon", action="store_true")
    g.add_argument("--lifetime", type=float, default=20.0)
    j = sub.add_parser("job")
    j.add_argument("--sentinel", required=True)
    j.add_argument("--job", type=int, required=True)
    h = sub.add_parser("helper")
    h.add_argument("--lifetime", type=float, default=20.0)
    h.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    {"agent": cmd_agent, "job": cmd_job, "helper": cmd_helper}[a.cmd](a)


if __name__ == "__main__":
    main()
