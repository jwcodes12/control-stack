#!/usr/bin/env python3
"""SC-27 anchor chain: the evidence-log writer (prereg/SC27-ANCHOR-CHAIN.md).

Owns the storage directory (one file log-<name>.jsonl per log). {"op": "append", "log", "entry"} appends the entry
with its chain head and fsyncs; {"op": "publish_head", "log", "head"} records a head the WRITER itself vouches for
in its published-heads file (the self-anchoring of the self_signed control). The writer controls its storage, so the
test harness, playing the writer-side adversary, may also rewrite these files directly. Self-contained apart from
chain.py; self-exits after --lifetime seconds.
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
    ap.add_argument("--store", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import chain
    os.makedirs(a.store, mode=0o700, exist_ok=True)
    lock = threading.Lock()

    def handle(m):
        name = str(m.get("log"))
        path = os.path.join(a.store, "log-%s.jsonl" % name)
        with lock:
            if m.get("op") == "append":
                entries = chain.read_entries(path)
                h = chain.step(chain.head_of(entries), m["entry"])
                with open(path, "a") as fh:
                    fh.write(json.dumps({"i": len(entries), "entry": m["entry"], "head": h}) + "\n")
                    fh.flush()
                    os.fsync(fh.fileno())
                return {"ok": True, "head": h, "n": len(entries) + 1, "t": time.monotonic_ns()}
            if m.get("op") == "publish_head":
                with open(os.path.join(a.store, "published-heads.jsonl"), "a") as fh:
                    fh.write(json.dumps({"log": name, "head": m["head"], "t": time.monotonic_ns()}) + "\n")
                return {"ok": True}
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
