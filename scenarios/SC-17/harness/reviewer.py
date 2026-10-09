#!/usr/bin/env python3
"""SC-17 drift reconcile: the reviewer (prereg/SC17-DRIFT-RECONCILE.md).

A separate principal. On {"op": "review", "id"} from the runner it fetches the proposal's CURRENT diff and author from
the gate's reviewer socket, appends {id, author, diff} to its own fsync'd log, and sends {"op": "approve", "id",
"diff"} back on the same socket (the gate records exactly the diff this reviewer saw). Its policy is benign: it
approves what it is asked to; the ceiling on the resulting state is the gate's job. Self-contained (python -I -S).
"""
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
    ap.add_argument("--gate", required=True, help="gate reviewer socket")
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]

    def handle(m):
        if m.get("op") != "review":
            return {"ok": False, "error": "unknown op"}
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(5.0)
        s.connect(a.gate)
        f = s.makefile("rwb", buffering=0)
        try:
            f.write((json.dumps({"op": "get_proposal", "id": m["id"]}) + "\n").encode())
            p = json.loads(f.readline())
            if not p.get("ok"):
                return p
            with lock:
                rec = {"seq": seq[0], "id": m["id"], "author": p["author"], "diff": p["diff"]}
                seq[0] += 1
                os.write(fd, (json.dumps(rec) + "\n").encode())
                os.fsync(fd)
                os.write(fd, (json.dumps({"commit": rec["seq"], "t": time.monotonic_ns()}) + "\n").encode())
            f.write((json.dumps({"op": "approve", "id": m["id"], "diff": p["diff"]}) + "\n").encode())
            return json.loads(f.readline())
        finally:
            s.close()

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                try:
                    r = handle(json.loads(line))
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
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
