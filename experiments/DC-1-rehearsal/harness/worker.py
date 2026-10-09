#!/usr/bin/env python3
"""DC-1 single-host rehearsal: a benign worker (preregistration prereg/DC1-REHEARSAL-SINGLEHOST.md).

Emits one small JSON effect line to the sink's Unix socket at most every 1/rate seconds (the next emission is
scheduled from the previous one's initiation stamp, so the worker never bursts to catch up: the model's `Rate`
premise holds by construction). Each effect carries the epoch the worker holds.

Control arrives on stdin, one command per line, from the controller:
  HALT      -> stop emitting (local and absorbing: the model's `HaltAbsorbs`); reports its receipt time
  EPOCH n   -> hold epoch n from now on (used only by the H4 token-leak control)
Reports go to stdout as lines "READY {...}", "HALTED {...}", "EPOCHSET {...}", "EXIT {...}". Times are this host's
CLOCK_MONOTONIC in ns (informational; the sink's stamps are the ones that are measured).

Self-contained (runs with python -I -S). Self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import select
import socket
import sys
import time


def say(tag, obj):
    sys.stdout.write(tag + " " + json.dumps(obj) + "\n")
    sys.stdout.flush()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, required=True)
    ap.add_argument("--sink", required=True)
    ap.add_argument("--rate", type=float, required=True, help="effects per second (upper bound)")
    ap.add_argument("--epoch", type=int, required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    gap_ns = int(round(1e9 / a.rate))
    t_end = time.monotonic() + a.lifetime
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.connect(a.sink)
    epoch, seq, halted = a.epoch, 0, False
    stdin_fd = sys.stdin.fileno()
    stdin_open, ibuf = True, b""
    last_ti = None
    say("READY", {"id": a.id, "pid": os.getpid(), "epoch": epoch})
    next_ns = time.monotonic_ns()
    try:
        while True:
            now = time.monotonic_ns()
            if now / 1e9 >= t_end:
                break
            if halted:
                wait = t_end - now / 1e9
            else:
                wait = max(0.0, (next_ns - now) / 1e9)
            r = []
            if stdin_open:
                r, _, _ = select.select([stdin_fd], [], [], wait)
            elif wait > 0:
                time.sleep(min(wait, 0.5))
            if r:
                chunk = os.read(stdin_fd, 4096)
                if not chunk:
                    stdin_open = False
                ibuf += chunk
                while b"\n" in ibuf:
                    line, ibuf = ibuf.split(b"\n", 1)
                    parts = line.decode().split()
                    if not parts:
                        continue
                    if parts[0] == "HALT" and not halted:
                        halted = True
                        say("HALTED", {"id": a.id, "t_rx": time.monotonic_ns(), "last_ti": last_ti, "seq": seq})
                    elif parts[0] == "EPOCH":
                        epoch = int(parts[1])
                        say("EPOCHSET", {"id": a.id, "t": time.monotonic_ns(), "epoch": epoch})
                continue
            if halted:
                continue
            ti = time.monotonic_ns()
            if ti < next_ns:
                continue
            s.sendall((json.dumps({"w": a.id, "s": seq, "e": epoch, "ti": ti}, separators=(",", ":")) + "\n")
                      .encode())
            last_ti = ti
            seq += 1
            next_ns = ti + gap_ns
    finally:
        say("EXIT", {"id": a.id, "t": time.monotonic_ns(), "seq": seq, "halted": halted})
        s.close()


if __name__ == "__main__":
    main()
