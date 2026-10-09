#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: the trusted verifier (prereg/SC19-TWO-PHASE.md).

{"op": "verify", "snap_id"}: fetch the snapshot record from the snapshot service, RESTORE the snapshot file into the
verifier's own scratch DB (SQLite backup API), run PRAGMA integrity_check, recompute every target's version, row
count and row hash from the restored copy, and mark the snapshot verified only if all match the record. The verified
record (with the per-target versions it vouches for) goes to the verifier's own fsync'd log, then a commit line.
{"op": "verified", "snap_id"} -> the verified record or none. Self-contained apart from dbutil.py.
"""
import argparse
import json
import os
import socket
import sys
import threading
import time


def rpc(path, obj, timeout=10.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        return json.loads(f.readline())
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--snapshot", required=True)
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import dbutil
    os.makedirs(a.scratch, mode=0o700, exist_ok=True)
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, verified, seq = threading.Lock(), {}, [0]

    def verify(sid):
        got = rpc(a.snapshot, {"op": "get", "snap_id": sid})
        if not got.get("ok"):
            return {"ok": False, "error": "no such snapshot"}
        rec = got["rec"]
        scratch = os.path.join(a.scratch, "restore-%s.db" % sid)
        if os.path.exists(scratch):
            os.unlink(scratch)
        src, dst = dbutil.connect(rec["file"]), dbutil.connect(scratch)
        try:
            src.backup(dst)
            integ = dst.execute("PRAGMA integrity_check").fetchone()[0]
            summ = dbutil.summary(dst)
        finally:
            src.close()
            dst.close()
        ok = integ == "ok" and summ == rec["targets"]
        with lock:
            out = {"seq": seq[0], "snap_id": sid, "verified": ok, "integrity": integ, "targets": summ,
                   "matches_record": summ == rec["targets"]}
            seq[0] += 1
            os.write(fd, (json.dumps(out) + "\n").encode())
            os.fsync(fd)
            os.write(fd, (json.dumps({"commit": out["seq"], "t": time.monotonic_ns()}) + "\n").encode())
            if ok:
                verified[sid] = out
        return {"ok": ok, "rec": out}

    def handle(m):
        if m.get("op") == "verify":
            return verify(m.get("snap_id"))
        if m.get("op") == "verified":
            with lock:
                r = verified.get(m.get("snap_id"))
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
