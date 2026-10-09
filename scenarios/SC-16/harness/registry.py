#!/usr/bin/env python3
"""SC-16 deploy admission: the artifact registry (prereg/SC16-DEPLOY-ADMISSION.md).

Two parts, one process, one Unix socket:
- a content-addressed store (CAS): `put` stores bytes under their SHA-256 (files named by digest); the FIRST stager
  of a digest is recorded in an append-only index (the model's `cas`, `casLookup` = first entry);
- a MUTABLE tag table that any client, including the agent, can write (`tag_set`), a stand-in for a pushable
  registry tag (the model's mutable staging `slots`).
The stager is the principal name of the connecting process, looked up from its kernel-reported (SO_PEERCRED) pid in
a principals file written by the runner. Ops (JSON line each way): put {data_b64}, get {digest}, tag_set {tag, digest},
tag_get {tag}. Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import base64
import hashlib
import json
import os
import socket
import struct
import sys
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--cas", required=True)
    ap.add_argument("--index", required=True)
    ap.add_argument("--principals", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    os.makedirs(a.cas, mode=0o700, exist_ok=True)
    lock = threading.Lock()
    stagers, tags = {}, {}
    ifd = os.open(a.index, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)

    def principal(pid):
        try:
            return json.load(open(a.principals)).get(str(pid), "unknown:%d" % pid)
        except (OSError, ValueError):
            return "unknown:%d" % pid

    def handle(m, pid):
        op = m.get("op")
        if op == "put":
            data = base64.b64decode(m["data_b64"])
            d = hashlib.sha256(data).hexdigest()
            with lock:
                path = os.path.join(a.cas, d)
                if d not in stagers:
                    tmp = path + ".tmp"
                    with open(tmp, "wb") as fh:
                        fh.write(data)
                        fh.flush()
                        os.fsync(fh.fileno())
                    os.rename(tmp, path)
                    stagers[d] = principal(pid)
                    os.write(ifd, (json.dumps({"ev": "put", "digest": d, "stager": stagers[d],
                                               "t": time.monotonic_ns()}) + "\n").encode())
                    os.fsync(ifd)
            return {"ok": True, "digest": d, "stager": stagers[d]}
        if op == "get":
            d = str(m.get("digest"))
            with lock:
                if d not in stagers:
                    return {"ok": False, "error": "no such digest"}
                data = open(os.path.join(a.cas, d), "rb").read()
            return {"ok": True, "data_b64": base64.b64encode(data).decode(), "stager": stagers[d]}
        if op == "tag_set":
            with lock:
                tags[m["tag"]] = m["digest"]
                os.write(ifd, (json.dumps({"ev": "tag", "tag": m["tag"], "digest": m["digest"],
                                           "by": principal(pid), "t": time.monotonic_ns()}) + "\n").encode())
            return {"ok": True}
        if op == "tag_get":
            with lock:
                d = tags.get(m.get("tag"))
            return {"ok": d is not None, "digest": d}
        return {"ok": False, "error": "unknown op"}

    def serve(conn):
        pid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))[0]
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                try:
                    r = handle(json.loads(line), pid)
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
    lis.listen(64)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
