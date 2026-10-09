#!/usr/bin/env python3
"""SC-07 sink: a plain TCP server that counts the bytes it receives (the independent observer).

Runs unprivileged (numeric UID) inside the sink namespace. For every accepted connection it records the peer, the
received byte count, the SHA-256 of the received bytes, and a timeline of (CLOCK_MONOTONIC time, cumulative bytes)
at every recv. At EOF from the client it replies one line "OK <bytes> <sha256>\\n" and closes. It writes its state
atomically to --state every 50 ms while anything changed (totals only), and a final state including the timelines
on SIGTERM or after --lifetime seconds. Open connections are aborted (SO_LINGER 0) at exit so no orphaned socket
outlives the process. Benign by construction; stdlib only; Python 3.9 compatible.
"""
import argparse
import hashlib
import json
import os
import selectors
import signal
import socket
import struct
import sys
import time

RECV = 262144
WRITE_EVERY = 0.05


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bind", required=True)
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--state", required=True)
    ap.add_argument("--label", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()

    stop = {"flag": False}
    signal.signal(signal.SIGTERM, lambda s, f: stop.update(flag=True))
    ls = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    ls.bind((a.bind, a.port))
    ls.listen(16)
    ls.setblocking(False)
    sel = selectors.DefaultSelector()
    sel.register(ls, selectors.EVENT_READ)
    conns, order = {}, []
    t_start = time.monotonic()
    deadline = t_start + a.lifetime

    def snapshot(final):
        out = {"label": a.label, "bind": a.bind, "port": a.port, "pid": os.getpid(), "uid": os.getuid(),
               "final": final, "t_written": time.monotonic(), "total_bytes": 0, "conns": []}
        for c in order:
            d = {k: c[k] for k in ("id", "peer", "bytes", "t_open", "t_first", "t_last", "closed", "ack_sent")}
            d["sha256"] = c["h"].hexdigest()
            if final:
                d["timeline"] = c["timeline"]
            out["conns"].append(d)
            out["total_bytes"] += c["bytes"]
        return out

    def write(final):
        tmp = a.state + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(snapshot(final), fh)
        os.replace(tmp, a.state)

    def finish(s, c, how):
        c["closed"] = how
        try:
            sel.unregister(s)
        except (KeyError, ValueError):
            pass
        s.close()

    write(False)
    print("READY " + json.dumps({"pid": os.getpid(), "label": a.label, "bind": a.bind, "port": a.port}), flush=True)
    dirty, last_write = False, time.monotonic()
    while not stop["flag"] and time.monotonic() < deadline:
        for key, _ in sel.select(0.02):
            s = key.fileobj
            if s is ls:
                try:
                    cs, peer = ls.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                cs.setblocking(False)
                c = {"id": len(order), "peer": "%s:%d" % peer, "bytes": 0, "h": hashlib.sha256(),
                     "t_open": time.monotonic(), "t_first": None, "t_last": None, "closed": None,
                     "ack_sent": False, "timeline": []}
                conns[cs] = c
                order.append(c)
                sel.register(cs, selectors.EVENT_READ)
                dirty = True
                continue
            c = conns[s]
            try:
                data = s.recv(RECV)
            except (BlockingIOError, InterruptedError):
                continue
            except OSError as e:
                finish(s, c, "error:%s" % e.__class__.__name__)
                dirty = True
                continue
            now = time.monotonic()
            if data:
                c["bytes"] += len(data)
                c["h"].update(data)
                c["t_first"] = c["t_first"] or now
                c["t_last"] = now
                c["timeline"].append([round(now, 6), c["bytes"]])
            else:
                s.setblocking(True)
                s.settimeout(1.0)
                try:
                    s.sendall(("OK %d %s\n" % (c["bytes"], c["h"].hexdigest())).encode())
                    c["ack_sent"] = True
                except OSError:
                    pass
                finish(s, c, "eof")
            dirty = True
        if dirty and time.monotonic() - last_write >= WRITE_EVERY:
            write(False)
            dirty, last_write = False, time.monotonic()
    for s, c in list(conns.items()):
        if c["closed"] is None:
            try:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
            except OSError:
                pass
            finish(s, c, "aborted-at-exit")
    ls.close()
    write(True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
