#!/usr/bin/env python3
"""SC-17 drift reconcile: the "cluster" holding the LIVE grant set (prereg/SC17-DRIFT-RECONCILE.md).

Two Unix sockets, one JSON line each way:
  oob.sock  out-of-band API (anyone, including the test's drift injector): {"op": "add", "grant": [s, v, r]}
  ctl.sock  trusted writers (apply gate, reconciler): {"op": "set_state", "grants": [...], "version": n, "by": ...}
            applied iff version >= the version of the last set_state (a stale reconciler push never undoes an apply)
  both      {"op": "get"} -> {"live", "base", "version"}; base = the last state pushed through ctl.sock
Every mutation is appended to the cluster's own log with a CLOCK_MONOTONIC stamp and the full live set after it,
so the live state at every instant can be reconstructed. Self-contained (python -I -S); self-exits after --lifetime.
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
    ap.add_argument("--dir", required=True)
    ap.add_argument("--init", required=True, help="JSON list of initial grants")
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    lock = threading.Lock()
    live = {tuple(g) for g in json.load(open(a.init))}
    base, version, seq = set(live), [0], [0]
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)

    def log(kind, **kw):
        rec = dict(seq=seq[0], t=time.monotonic_ns(), kind=kind, live=sorted(live), base=sorted(base),
                   version=version[0], **kw)
        os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        seq[0] += 1

    def handle(m, role):
        nonlocal live, base
        op = m.get("op")
        with lock:
            if op == "get":
                return {"ok": True, "live": sorted(live), "base": sorted(base), "version": version[0],
                        "t": time.monotonic_ns()}
            if op == "add" and role == "oob":
                g = tuple(m["grant"])
                new = g not in live
                live.add(g)
                log("oob_add", grant=list(g), new=new)
                return {"ok": True}
            if op == "set_state" and role == "ctl":
                if int(m["version"]) < version[0]:
                    log("stale_push_refused", by=m.get("by"), pushed_version=m["version"])
                    return {"ok": False, "error": "stale version"}
                before = set(live)
                live = {tuple(g) for g in m["grants"]}
                base = set(live)
                version[0] = int(m["version"])
                log("set_state", by=m.get("by"), removed=sorted(before - live), added=sorted(live - before))
                return {"ok": True, "removed": sorted(before - live)}
        return {"ok": False, "error": "op not allowed on this socket"}

    def serve(conn, role):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                try:
                    r = handle(json.loads(line), role)
                except Exception as e:
                    r = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
        except OSError:
            pass
        finally:
            conn.close()

    def listen(role):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
        s.listen(64)
        while True:
            conn, _ = s.accept()
            threading.Thread(target=serve, args=(conn, role), daemon=True).start()

    with lock:
        log("init")
    for role in ("oob", "ctl"):
        threading.Thread(target=listen, args=(role,), daemon=True).start()
    time.sleep(0.05)
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    time.sleep(a.lifetime)
    os._exit(0)


if __name__ == "__main__":
    main()
