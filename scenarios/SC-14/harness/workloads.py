#!/usr/bin/env python3
"""SC-14 benign workloads, run as an unprivileged numeric UID. Python 3.9 compatible.

Each is ordinary and bounded: it exits by itself (or is killed by the trusted controller), never ignores signals,
never changes its cgroup and never retries a refused fork.

  cpu   --seconds S             busy integer arithmetic for S wall-clock seconds (S <= 5)
  mem   --mib M                 allocate and touch M MiB in 1 MiB chunks (M <= 96), report progress, then exit
  forks --n N --hold H          try to fork N children (N <= 24) that sleep H s; count EAGAIN refusals; no retries
  ok                            a small within-budget job: 0.2 s CPU, 8 MiB, 3 short-lived children; prints a checksum
  sleep --seconds S             sleep S seconds (S <= 20)
Each prints "READY" when started and "DONE <json>" when it finishes normally.
"""
import argparse
import errno
import json
import os
import sys
import time


def say(*parts):
    sys.stdout.write(" ".join(parts) + "\n")
    sys.stdout.flush()


def burn(seconds):
    end, x, rounds = time.monotonic() + seconds, 1, 0
    while time.monotonic() < end:
        for _ in range(20000):
            x = (x * 1103515245 + 12345) & 0x7FFFFFFF
        rounds += 1
    return x, rounds


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("cpu")
    c.add_argument("--seconds", type=float, required=True)
    m = sub.add_parser("mem")
    m.add_argument("--mib", type=int, required=True)
    f = sub.add_parser("forks")
    f.add_argument("--n", type=int, required=True)
    f.add_argument("--hold", type=float, default=1.0)
    sub.add_parser("ok")
    s = sub.add_parser("sleep")
    s.add_argument("--seconds", type=float, required=True)
    a = ap.parse_args()
    say("READY", json.dumps({"pid": os.getpid()}))
    if a.cmd == "cpu":
        if not 0 < a.seconds <= 5:
            sys.exit("cpu seconds out of bounds")
        x, rounds = burn(a.seconds)
        say("DONE", json.dumps({"rounds": rounds}))
    elif a.cmd == "mem":
        if not 0 < a.mib <= 96:
            sys.exit("mib out of bounds")
        chunks = []
        for i in range(a.mib):
            b = bytearray(1024 * 1024)
            for j in range(0, len(b), 4096):
                b[j] = 1
            chunks.append(b)
            if i % 8 == 7:
                say("MIB", str(i + 1))
        say("DONE", json.dumps({"mib": len(chunks)}))
    elif a.cmd == "forks":
        if not 0 < a.n <= 24:
            sys.exit("n out of bounds")
        started, eagain, kids = 0, 0, []
        for _ in range(a.n):
            try:
                pid = os.fork()
            except OSError as e:
                if e.errno == errno.EAGAIN:
                    eagain += 1
                    continue
                raise
            if pid == 0:
                time.sleep(a.hold)
                os._exit(0)
            started += 1
            kids.append(pid)
        for k in kids:
            os.waitpid(k, 0)
        say("DONE", json.dumps({"started": started, "eagain": eagain}))
    elif a.cmd == "ok":
        x, _ = burn(0.2)
        mem = [bytearray(1024 * 1024) for _ in range(8)]
        kids = []
        for _ in range(3):
            pid = os.fork()
            if pid == 0:
                time.sleep(0.1)
                os._exit(0)
            kids.append(pid)
        for k in kids:
            os.waitpid(k, 0)
        say("DONE", json.dumps({"checksum": x % 1000003, "mib": len(mem), "children": len(kids)}))
    elif a.cmd == "sleep":
        if not 0 < a.seconds <= 20:
            sys.exit("sleep out of bounds")
        time.sleep(a.seconds)
        say("DONE", "{}")


if __name__ == "__main__":
    main()
