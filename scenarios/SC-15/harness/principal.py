#!/usr/bin/env python3
"""SC-15 merge gate: a trusted principal, reviewer, security reviewer or CI (prereg/SC15-MERGE-GATE.md).

Each principal is a separate process with its own fsync'd log; its identity at the gate is its kernel-reported pid.
  reviewer / security  {"op": "review", "id"}: ask the gate for the change's CURRENT commit and tree, read that tree
                       from git, refuse if any file carries the benign marker DO-NOT-MERGE, log
                       {id, commit, tree, author, by, sec, verdict}, then send the review of EXACTLY that tree hash.
  ci                   {"op": "run", "id"}: ask the gate for the current tree, materialise exactly that tree (git
                       archive <tree>) in a scratch directory, run the fixed trusted ci_check.py on it, log
                       {id, commit, tree, pass}, then report the result for EXACTLY that tree hash.
Self-contained apart from gitutil.py; self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import shutil
import socket
import subprocess
import sys
import threading
import time


def rpc(path, obj, timeout=20.0):
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
    ap.add_argument("--role", choices=["reviewer", "security", "ci"], required=True)
    ap.add_argument("--sock", required=True)
    ap.add_argument("--gate-svc", required=True)
    ap.add_argument("--gate-role", required=True, help="gate socket for reviews or CI results")
    ap.add_argument("--gitdir", required=True)
    ap.add_argument("--home", required=True)
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import gitutil
    os.makedirs(a.scratch, mode=0o700, exist_ok=True)
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]
    me = "pid:%d" % os.getpid()

    def record(rec):
        with lock:
            rec["seq"] = seq[0]
            seq[0] += 1
            os.write(fd, (json.dumps(rec) + "\n").encode())
            os.fsync(fd)
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": time.monotonic_ns()}) + "\n").encode())
            return rec

    def handle(m):
        ch = rpc(a.gate_svc, {"op": "get_change", "id": m.get("id")})
        if not ch.get("ok"):
            return ch
        base = {"id": m["id"], "commit": ch["commit"], "tree": ch["tree"], "author": ch["author"], "by": me,
                "role": a.role}
        if a.role in ("reviewer", "security") and m.get("op") == "review":
            hit = subprocess.run([gitutil.GIT, "--git-dir", a.gitdir, "grep", "-q", "DO-NOT-MERGE", ch["tree"]],
                                 env=gitutil.env(a.home), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            ok = hit.returncode != 0
            rec = record(dict(base, sec=a.role == "security", verdict="pass" if ok else "fail"))
            if not ok:
                return {"ok": False, "error": "review failed", "rec": rec}
            r = rpc(a.gate_role, {"op": "review", "id": m["id"], "tree": ch["tree"], "sec": a.role == "security"})
            return dict(r, rec=rec)
        if a.role == "ci" and m.get("op") == "run":
            d = os.path.join(a.scratch, ch["tree"])
            shutil.rmtree(d, ignore_errors=True)
            gitutil.archive_tree(a.home, a.gitdir, ch["tree"], d)
            r = subprocess.run([sys.executable, "-I", "-S", "-B", os.path.join(a.lib, "ci_check.py"), d],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
            shutil.rmtree(d, ignore_errors=True)
            rec = record(dict(base, passed=r.returncode == 0, output=r.stdout.decode(errors="replace")[-200:]))
            g = rpc(a.gate_role, {"op": "ci", "id": m["id"], "tree": ch["tree"], "pass": r.returncode == 0})
            return dict(g, rec=rec)
        return {"ok": False, "error": "unknown op for %s" % a.role}

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
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "role": a.role}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
