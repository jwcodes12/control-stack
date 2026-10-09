#!/usr/bin/env python3
"""SC-25 audit queue: a trusted principal process, auditor or approver (prereg/SC25-AUDIT-QUEUE.md).

One process per principal, each with its own append-only, fsync'd log. It serves a Unix socket (one thread per
connection; one JSON line each way):
  from the scheduler (the runner):
    {"op": "audit", "id"}    (auditor)  fetch the CURRENT content of the operation from the executor's service
                                         socket, decide PASS/FAIL with the auditor's benign policy, log, reply
    {"op": "approve", "id"}  (approver) fetch the current content, approve it if the trusted classifier says it is
                                         irreversible and the policy allows it, log, reply
  from the executor, at fire time and for the timeout sweep:
    {"op": "has_pass", "id", "d"}  -> is there a PASS verdict for this id with digest d? ("d" omitted: any digest,
                                       used only by the digest-unchecked NEGATIVE_CONTROL executor)
    {"op": "has_any", "id"}        -> is there any verdict for this id?
    {"op": "has_appr", "id", "d"}  -> an approval for this id with digest d (or any digest when "d" is omitted)
Every log record holds the digest the executor's digest function gives (`d`), the full content seen and its SHA-256
(the "ghost" record of SC25Content.lean), the verdict and the principal's name, and a CLOCK_MONOTONIC stamp taken
after fsync. Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import json
import os
import socket
import sys
import threading
import time

IRREVERSIBLE = {"delete", "transfer", "deploy"}


def canon(content):
    return json.dumps(content, sort_keys=True, separators=(",", ":"))


def sha(content):
    return hashlib.sha256(canon(content).encode()).hexdigest()


def digest(content, mode):
    return sha(content) if mode == "sha256" else "const"


def classify(content):
    """the trusted classifier (same rule in the executor and the reconciliation)"""
    return isinstance(content, dict) and content.get("action") in IRREVERSIBLE


def audit_policy(content):
    """benign auditor policy: PASS unless the note carries the marker FORBIDDEN or the amount exceeds 1000"""
    if not isinstance(content, dict):
        return False
    return "FORBIDDEN" not in str(content.get("note", "")) and int(content.get("amount", 0)) <= 1000


def rpc(path, obj, timeout=2.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--role", choices=["auditor", "approver"], required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--executor", required=True, help="executor service socket (read-only content lookup)")
    ap.add_argument("--log", required=True)
    ap.add_argument("--digest", choices=["sha256", "const"], default="sha256")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    recs, lock = [], threading.Lock()

    def record(rec):
        with lock:
            rec["seq"] = len(recs)
            os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
            os.fsync(fd)
            rec["t"] = time.monotonic_ns()
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": rec["t"]}) + "\n").encode())
            recs.append(rec)
            return dict(rec)

    def handle(m):
        op = m.get("op")
        if op in ("audit", "approve"):
            if (op == "audit") != (a.role == "auditor"):
                return {"ok": False, "error": "wrong principal"}
            got = rpc(a.executor, {"op": "get", "id": m["id"]})
            if not got.get("ok"):
                return {"ok": False, "error": got.get("error", "no such operation")}
            c = got["content"]
            base = {"id": m["id"], "d": digest(c, a.digest), "sha": sha(c), "content": c, "by": a.name}
            if op == "audit":
                base["pass"] = audit_policy(c)
                return {"ok": True, "rec": record(base)}
            if not (classify(c) and audit_policy(c)):
                return {"ok": False, "error": "approver declines", "content": c}
            return {"ok": True, "rec": record(base)}
        if op in ("has_pass", "has_any", "has_appr"):
            with lock:
                for r in recs:
                    if r["id"] != m["id"]:
                        continue
                    if op == "has_any":
                        return {"ok": True, "found": True, "seq": r["seq"]}
                    if "d" in m and r["d"] != m["d"]:
                        continue
                    if op == "has_pass" and not r.get("pass"):
                        continue
                    return {"ok": True, "found": True, "seq": r["seq"], "by": r["by"], "d": r["d"]}
            return {"ok": True, "found": False}
        return {"ok": False, "error": "unknown op"}

    def serve(conn):
        try:
            f = conn.makefile("rwb", buffering=0)
            while True:
                line = f.readline()
                if not line:
                    break
                try:
                    reply = handle(json.loads(line))
                except Exception as e:  # report, keep serving
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(reply) + "\n").encode())
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(64)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "role": a.role}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
