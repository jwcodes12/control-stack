#!/usr/bin/env python3
"""SC-06 shared artifacts: the user (prereg/SC06-SHARED-ARTIFACTS.md). Confirms {"op": "confirm", agent, tool, value}
iff exactly that triple is in its own list of intended actions; every decision goes to its own fsync'd log (record,
then a {"commit": seq, "t"} line). Self-contained."""
import argparse
import json
import os
import socket
import sys
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--intent", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    intent = {tuple(x) for x in json.load(open(a.intent))}
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]

    def handle(m):
        ok = (m.get("agent"), m.get("tool"), m.get("value")) in intent
        with lock:
            rec = {"seq": seq[0], "agent": m.get("agent"), "tool": m.get("tool"), "value": m.get("value"),
                   "approved": ok}
            seq[0] += 1
            os.write(fd, (json.dumps(rec) + "\n").encode())
            os.fsync(fd)
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": time.monotonic_ns()}) + "\n").encode())
        return {"ok": True, "approved": ok, "conf": rec["seq"]}

    def serve(conn):
        f = conn.makefile("rwb")
        try:
            for line in f:
                f.write((json.dumps(handle(json.loads(line))) + "\n").encode())
                f.flush()
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(8)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
