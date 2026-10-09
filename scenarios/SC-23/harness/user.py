#!/usr/bin/env python3
"""SC-23 taint scaffold: the user (prereg/SC23-TAINT-SCAFFOLD.md).

A separate process standing in for the human user. From a task file it knows, per task, the trusted inputs it gives
(for example the invoice id and its own account number) and the exact sensitive call it intends
({"tool", "vals"}). It answers the runtime only:
  {"op": "input", "task"}                  -> the task's trusted inputs (logged)
  {"op": "confirm", "task", "tool", "vals"} -> approved iff (tool, vals) equal its intent EXACTLY (logged, with a
                                               confirmation id)
Every record goes to its own append-only file with fsync, followed by a {"commit": seq, "t": ns} line. This log is
the reconciliation's source of truth for confirmations. Self-contained (python -I -S).
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
    ap.add_argument("--tasks", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    tasks = json.load(open(a.tasks))
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]

    def record(rec):
        with lock:
            rec["seq"] = seq[0]
            seq[0] += 1
            os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
            os.fsync(fd)
            t = time.monotonic_ns()
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": t}) + "\n").encode())
            return rec["seq"], t

    def handle(m):
        t = tasks.get(m.get("task"))
        if t is None:
            return {"ok": False, "error": "unknown task"}
        if m.get("op") == "input":
            s, _ = record({"kind": "input", "task": m["task"], "inputs": t["inputs"]})
            return {"ok": True, "inputs": t["inputs"], "seq": s}
        if m.get("op") == "confirm":
            exp = t.get("expect")
            approved = exp is not None and exp["tool"] == m.get("tool") and exp["vals"] == m.get("vals")
            s, tc = record({"kind": "confirm", "task": m["task"], "tool": m.get("tool"), "vals": m.get("vals"),
                            "approved": approved})
            return {"ok": True, "approved": approved, "conf": s, "t": tc}
        return {"ok": False, "error": "unknown op"}

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                f.write((json.dumps(handle(json.loads(line))) + "\n").encode())
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
