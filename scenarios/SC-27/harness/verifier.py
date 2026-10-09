#!/usr/bin/env python3
"""SC-27 anchor chain: the manifest verifier (prereg/SC27-ANCHOR-CHAIN.md).

{"op": "verify", "log", "entries"}: recompute the chain head of the manifest's entries and accept iff that head
EQUALS a head the independent witness anchored for that log (read from the witness's own log, read-only). An
anchored prefix plus extra entries is not accepted (exact match only). Every decision is appended to the verifier's
own log. NEGATIVE_CONTROL flags:
  --current-head  accept iff the head equals the head of the writer's CURRENT storage   (no_anchor_rollback_breaks)
  --writer-heads  also accept heads the writer published itself                          (self_signed_breaks)
Self-contained apart from chain.py.
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
    ap.add_argument("--witness-log", required=True)
    ap.add_argument("--store", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--current-head", action="store_true")
    ap.add_argument("--writer-heads", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import chain
    config = {"current_head": a.current_head, "writer_heads": a.writer_heads}
    lock = threading.Lock()
    logf = open(a.log, "a", buffering=1)

    def anchored(name):
        out = set()
        if os.path.exists(a.witness_log):
            for line in open(a.witness_log):
                r = json.loads(line)
                if r.get("kind") == "anchor" and r.get("log") == name:
                    out.add(r["head"])
        return out

    def verify(m):
        name, entries = str(m["log"]), m["entries"]
        h = chain.head_of(entries)
        if a.current_head:
            ok = h == chain.head_of(chain.read_entries(os.path.join(a.store, "log-%s.jsonl" % name)))
            why = "head equals the writer's current storage" if ok else "head differs from current storage"
        else:
            src = anchored(name)
            if a.writer_heads:
                p = os.path.join(a.store, "published-heads.jsonl")
                if os.path.exists(p):
                    src |= {json.loads(l)["head"] for l in open(p) if json.loads(l)["log"] == name}
            ok = h in src
            why = "head anchored" if ok else "head not anchored by the witness"
        rec = {"log": name, "head": h, "n": len(entries), "accepted": ok, "why": why, "config": config,
               "t": time.monotonic_ns()}
        with lock:
            logf.write(json.dumps(rec) + "\n")
        return {"ok": True, "accepted": ok, "head": h, "why": why}

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                m = json.loads(line)
                try:
                    r = verify(m) if m.get("op") == "verify" else {"ok": False, "error": "unknown op"}
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
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
