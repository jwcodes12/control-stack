#!/usr/bin/env python3
"""SC-10/11 enforcement point: an egress-decision service (prereg/SC10-POLICY-STORE.md).

{"op": "decide", "host"} on decide.sock. Deployed configuration (model `full`, `fresh` and `singleEval`): for EVERY
decision it asks the store for the LATEST version (no cache) and allows iff the host is in that version's "allow" list;
it logs {host, decision, version, digest, length, t_answer}. NEGATIVE_CONTROL flags:
  --cache-ttl S   use a cached copy refreshed at most every S seconds          (`stale_cache_breaks`)
  --alt-file F    decide from an agent-writable policy file instead of the store (`alternate_evaluator_breaks`)
Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import socket
import sys
import threading
import time


def rpc(path, obj, timeout=5.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb")
        f.write((json.dumps(obj) + "\n").encode())
        f.flush()
        return json.loads(f.readline())
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--store", required=True, help="store read socket")
    ap.add_argument("--log", required=True)
    ap.add_argument("--cache-ttl", type=float, default=None)
    ap.add_argument("--alt-file", default=None)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"cache_ttl": a.cache_ttl, "alt_file": a.alt_file is not None}
    lock = threading.Lock()
    logf = open(a.log, "a", buffering=1)
    cache = {"rec": None, "t": 0.0}

    def decide(host):
        if a.alt_file:
            pol = json.load(open(a.alt_file))
            rec = {"version": None, "digest": None, "length": None, "t_answer": time.monotonic_ns(), "policy": pol}
        elif a.cache_ttl is not None:
            if cache["rec"] is None or time.monotonic() - cache["t"] >= a.cache_ttl:
                cache["rec"], cache["t"] = rpc(a.store, {"op": "latest"}), time.monotonic()
            rec = dict(cache["rec"], t_answer=time.monotonic_ns())   # the moment the (cached) policy is applied
        else:
            rec = rpc(a.store, {"op": "latest"})
        allowed = host in rec["policy"].get("allow", [])
        out = {"host": host, "decision": "allow" if allowed else "deny", "version": rec["version"],
               "digest": rec["digest"], "length": rec["length"], "t_answer": rec["t_answer"],
               "t_decide": time.monotonic_ns(), "config": config}
        with lock:
            logf.write(json.dumps(out) + "\n")
        return out

    def serve(conn):
        f = conn.makefile("rwb")
        try:
            for line in f:
                m = json.loads(line)
                try:
                    r = decide(m["host"]) if m.get("op") == "decide" else {"error": "unknown op"}
                except Exception as e:
                    r = {"error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
                f.flush()
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
