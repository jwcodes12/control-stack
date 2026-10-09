#!/usr/bin/env python3
"""SC-27 anchor chain: the independent anchoring witness (prereg/SC27-ANCHOR-CHAIN.md).

Reads the writer's storage READ-ONLY, recomputes each log's chain head itself (it never trusts stored heads), and
appends anchors to its OWN log in its own directory (fsync, then a commit line). Every --period seconds (0 = only on
request) and on {"op": "anchor_now", "log"} it examines each log:
  - nothing new (same length, same head): no record;
  - an EXTENSION of the last anchored state of that log (at least as long, and the prefix of the previous length has
    the previously anchored head): record {"kind": "anchor", log, head, n};
  - anything else (modified, reordered or truncated after anchoring): record {"kind": "fork", ...} and do NOT anchor.
The fork check is an append-only consistency check BEYOND the model (SC27Chain's witness anchors whatever storage
holds); it keeps a periodic witness from later anchoring tampered storage. Self-contained apart from chain.py.
"""
import argparse
import glob
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
    ap.add_argument("--log", required=True)
    ap.add_argument("--period", type=float, default=0.0)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import chain
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, last, seq = threading.Lock(), {}, [0]

    def record(rec):
        rec["seq"] = seq[0]
        seq[0] += 1
        os.write(fd, (json.dumps(rec) + "\n").encode())
        os.fsync(fd)
        t = time.monotonic_ns()
        os.write(fd, (json.dumps({"commit": rec["seq"], "t": t}) + "\n").encode())
        rec["t"] = t
        return rec

    def examine(name):
        path = os.path.join(a.store, "log-%s.jsonl" % name)
        with lock:
            entries = chain.read_entries(path)
            if not entries:
                return {"kind": "empty"}
            hs = chain.heads(entries)
            prev = last.get(name)
            if prev is not None:
                n0, h0 = prev
                if len(entries) == n0 and hs[-1] == h0:
                    return {"kind": "unchanged", "head": h0, "n": n0}
                if len(entries) < n0 or hs[n0 - 1] != h0:
                    return record({"kind": "fork", "log": name, "head": hs[-1], "n": len(entries),
                                   "anchored_head": h0, "anchored_n": n0})
            last[name] = (len(entries), hs[-1])
            return record({"kind": "anchor", "log": name, "head": hs[-1], "n": len(entries)})

    def periodic():
        t0 = time.monotonic()
        j = 1
        while True:
            time.sleep(max(0.0, t0 + j * a.period - time.monotonic()))
            j += 1
            for p in sorted(glob.glob(os.path.join(a.store, "log-*.jsonl"))):
                examine(os.path.basename(p)[4:-6])

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                m = json.loads(line)
                try:
                    r = ({"ok": True, "rec": examine(str(m["log"]))} if m.get("op") == "anchor_now"
                         else {"ok": False, "error": "unknown op"})
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
    if a.period > 0:
        threading.Thread(target=periodic, daemon=True).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "period": a.period}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
