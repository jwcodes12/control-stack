#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: the benign concurrent writer (prereg/SC19-TWO-PHASE.md).

Adds rows to targets of the production DB, each write in its own IMMEDIATE transaction that bumps the target's
version and records a history row. Commands on a Unix socket: {"op": "write", "target", "n"}. With --background
TARGETS it also writes one row to a random one of those targets every --interval seconds. Self-contained apart
from dbutil.py (python -I -S, directory passed with --lib); self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import random
import socket
import sys
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--db", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--background", default="")
    ap.add_argument("--interval", type=float, default=0.02)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import dbutil
    lock = threading.Lock()
    logf = open(a.log, "a", buffering=1)

    def write(t, n, why):
        with lock:
            c = dbutil.connect(a.db)
            try:
                c.execute("BEGIN IMMEDIATE")
                v = dbutil.write_rows(c, t, n)
                c.execute("COMMIT")
            finally:
                c.close()
            logf.write(json.dumps({"t": time.monotonic_ns(), "target": t, "n": n, "ver_after": v, "why": why}) + "\n")
            return v

    def bg():
        ts = [x for x in a.background.split(",") if x]
        rnd = random.Random(1)
        while ts:
            time.sleep(a.interval)
            write(rnd.choice(ts), 1, "background")

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                m = json.loads(line)
                try:
                    r = {"ok": True, "ver": write(m["target"], int(m["n"]), "command")}
                except Exception as e:
                    r = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(16)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    threading.Thread(target=bg, daemon=True).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
