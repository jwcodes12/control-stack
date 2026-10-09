#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: the snapshot service (prereg/SC19-TWO-PHASE.md).

{"op": "snapshot"} copies the WHOLE production DB into the snapshot store with SQLite's online backup API (a
consistent copy), then records, per target, the version, row count and row hash read FROM THE COPY. The record goes
to its own fsync'd log. {"op": "get", "snap_id"} returns a record. Self-contained apart from dbutil.py.
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
    ap.add_argument("--lib", required=True)
    ap.add_argument("--db", required=True)
    ap.add_argument("--store", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import dbutil
    os.makedirs(a.store, mode=0o700, exist_ok=True)
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, recs = threading.Lock(), {}

    def snapshot():
        with lock:
            sid = "snap-%03d" % len(recs)
            path = os.path.join(a.store, sid + ".db")
            src, dst = dbutil.connect(a.db), dbutil.connect(path)
            try:
                src.backup(dst)
                summ = dbutil.summary(dst)
            finally:
                src.close()
                dst.close()
            rec = {"snap_id": sid, "file": path, "targets": summ, "t": time.monotonic_ns()}
            os.write(fd, (json.dumps(rec) + "\n").encode())
            os.fsync(fd)
            recs[sid] = rec
            return rec

    def handle(m):
        if m.get("op") == "snapshot":
            return {"ok": True, "rec": snapshot()}
        if m.get("op") == "get":
            r = recs.get(m.get("snap_id"))
            return {"ok": r is not None, "rec": r}
        return {"ok": False, "error": "unknown op"}

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
