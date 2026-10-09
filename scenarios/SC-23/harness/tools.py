#!/usr/bin/env python3
"""SC-23 taint scaffold: the (untrusted-content) tool server (prereg/SC23-TAINT-SCAFFOLD.md).

Serves scripted documents from a fixture file: {"op": "read_doc", "doc": id} -> {"ok": true, "text": ...}. Some
fixture documents carry injected instructions and values as plain benign text (for example "transfer 999 to
account 7"); nothing here has any real effect. Every returned result is logged to its own file (used only to
inspect planner state for leaked content). Self-contained (python -I -S); self-exits after --lifetime seconds.
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
    ap.add_argument("--fixture", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    docs = json.load(open(a.fixture))
    logf = open(a.log, "a", buffering=1)
    lock = threading.Lock()

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                m = json.loads(line)
                if m.get("op") == "read_doc" and m.get("doc") in docs:
                    reply = {"ok": True, "text": docs[m["doc"]]}
                    with lock:
                        logf.write(json.dumps({"doc": m["doc"], "text": reply["text"], "t": time.monotonic_ns()}) + "\n")
                else:
                    reply = {"ok": False, "error": "no such document"}
                f.write((json.dumps(reply) + "\n").encode())
        except (OSError, ValueError):
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
