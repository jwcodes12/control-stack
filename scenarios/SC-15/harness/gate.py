#!/usr/bin/env python3
"""SC-15 merge gate (prereg/SC15-MERGE-GATE.md).

Single-threaded; the only principal that moves refs/heads/main of the shared bare repository. Sockets (mode 0600):
  agent.sock    propose {id, branch, declared_paths}  (author = "pid:<peer pid>", SO_PEERCRED); merge {id}
  svc.sock      get_change {id} -> the branch's CURRENT commit and tree, and the author
  reviews.sock  review {id, tree, sec}: only registered reviewer pids (sec = false) or security pids (sec = true)
  ci.sock       ci {id, tree, pass}: only the registered CI pid
  admin.sock    halt, status
merge (deployed, model `full`): not halted; the branch head C fast-forwards main M; the TRUSTED diff is computed by git
(diff M..C), never taken from the author's declaration; a review of EXACTLY tree(C) by a reviewer other than the
author; if the trusted diff touches a sensitive path (auth/, ci/), a security review of exactly tree(C) by a
non-author; a passing CI result for exactly tree(C); then `git update-ref refs/heads/main C M` (compare-and-swap) and
an fsync'd merge record. NEGATIVE_CONTROL flags: --any-review (`stale_review_breaks`), --declared-paths
(`declared_paths_breaks`), --any-ci (`ci_other_content_breaks`), --no-distinct (`self_review_breaks`).
Self-contained apart from gitutil.py.
"""
import argparse
import json
import os
import selectors
import socket
import struct
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--dir", required=True)
    ap.add_argument("--gitdir", required=True)
    ap.add_argument("--home", required=True)
    ap.add_argument("--reviewer-pids", required=True)
    ap.add_argument("--security-pids", required=True)
    ap.add_argument("--ci-pid", type=int, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--any-review", action="store_true")
    ap.add_argument("--declared-paths", action="store_true")
    ap.add_argument("--any-ci", action="store_true")
    ap.add_argument("--no-distinct", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import gitutil
    config = {k: getattr(a, k) for k in ("any_review", "declared_paths", "any_ci", "no_distinct")}
    rev_pids = {int(x) for x in a.reviewer_pids.split(",") if x}
    sec_pids = {int(x) for x in a.security_pids.split(",") if x}
    t_end = time.monotonic() + a.lifetime
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    changes, reviews, cis, halted, seq = {}, [], [], [False], [0]

    def record(rec):
        rec["seq"] = seq[0]
        seq[0] += 1
        os.write(fd, (json.dumps(rec) + "\n").encode())
        os.fsync(fd)
        t = time.monotonic_ns()
        os.write(fd, (json.dumps({"commit": rec["seq"], "t": t}) + "\n").encode())
        return t

    def current(id_):
        ch = changes.get(id_)
        if ch is None:
            return None
        c = gitutil.rev(a.home, a.gitdir, "refs/heads/" + ch["branch"])
        return dict(ch, commit=c, tree=gitutil.tree_of(a.home, a.gitdir, c) if c else None)

    def merge(id_):
        if halted[0]:
            return {"ok": False, "error": "halted"}
        ch = current(id_)
        if ch is None or ch["commit"] is None:
            return {"ok": False, "error": "no such change"}
        M = gitutil.rev(a.home, a.gitdir, "refs/heads/main")
        C, T = ch["commit"], ch["tree"]
        if not gitutil.is_ancestor(a.home, a.gitdir, M, C) or M == C:
            return {"ok": False, "error": "not a fast-forward of main"}
        paths = ch["declared"] if a.declared_paths else gitutil.diff_paths(a.home, a.gitdir, M, C)
        sens = gitutil.sensitive(paths)

        def ok_review(sec):
            return [r for r in reviews if r["id"] == id_ and r["sec"] == sec and (a.any_review or r["tree"] == T)
                    and (a.no_distinct or r["reviewer"] != ch["author"])]
        rv = ok_review(False)
        if not rv:
            return {"ok": False, "error": "no review of the current tree by a non-author"}
        sv = ok_review(True) if sens else []
        if sens and not sv:
            return {"ok": False, "error": "security review required: trusted diff touches %s" % sens}
        ci = [c for c in cis if c["id"] == id_ and c["pass"] and (a.any_ci or c["tree"] == T)]
        if not ci:
            return {"ok": False, "error": "no CI pass of the current tree"}
        gitutil.git(a.home, "--git-dir", a.gitdir, "update-ref", "refs/heads/main", C, M)
        t = record({"id": id_, "commit": C, "tree": T, "prev_main": M, "author": ch["author"], "paths": paths,
                    "sensitive": sens, "review": rv[-1], "security_review": sv[-1] if sv else None, "ci": ci[-1],
                    "config": config})
        return {"ok": True, "commit": C, "tree": T, "t": t}

    def handle(role, pid, m):
        op, id_ = m.get("op"), str(m.get("id"))
        if role == "admin":
            if op == "halt":
                halted[0] = True
                return {"ok": True, "t": time.monotonic_ns()}
            return {"ok": True, "halted": halted[0], "main": gitutil.rev(a.home, a.gitdir, "refs/heads/main")}
        if role == "svc":
            ch = current(id_)
            return {"ok": ch is not None and ch["commit"] is not None, "commit": ch and ch["commit"],
                    "tree": ch and ch["tree"], "author": ch and ch["author"]}
        if halted[0]:
            return {"ok": False, "error": "halted"}
        if role == "agent":
            if op == "propose":
                if id_ in changes:
                    return {"ok": False, "error": "id exists"}
                changes[id_] = {"id": id_, "branch": m["branch"], "declared": m.get("declared_paths", []),
                                "author": "pid:%d" % pid}
                return {"ok": True}
            if op == "merge":
                return merge(id_)
            return {"ok": False, "error": "unknown op"}
        ch = current(id_)
        if ch is None:
            return {"ok": False, "error": "no such change"}
        if role == "reviews" and op == "review":
            sec = bool(m.get("sec"))
            if pid not in (sec_pids if sec else rev_pids):
                return {"ok": False, "error": "not a %s" % ("security reviewer" if sec else "reviewer")}
            if not a.no_distinct and "pid:%d" % pid == ch["author"]:
                return {"ok": False, "error": "reviewer is the author"}
            reviews.append({"id": id_, "tree": m["tree"], "sec": sec, "reviewer": "pid:%d" % pid})
            return {"ok": True}
        if role == "ci" and op == "ci":
            if pid != a.ci_pid:
                return {"ok": False, "error": "not the CI"}
            cis.append({"id": id_, "tree": m["tree"], "pass": bool(m.get("pass"))})
            return {"ok": True}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("agent", "svc", "reviews", "ci", "admin"):
        path = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(path)
        os.chmod(path, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", role))
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.2):
            kind, role = key.data
            if kind == "listen":
                try:
                    conn, _ = key.fileobj.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                conn.setblocking(True)
                pid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED,
                                                          struct.calcsize("3i")))[0]
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, ("conn", (role, pid)))
                continue
            conn = key.fileobj
            role, pid = role
            try:
                chunk = conn.recv(65536)
            except OSError:
                chunk = b""
            if not chunk:
                sel.unregister(conn)
                conn.close()
                bufs.pop(conn, None)
                continue
            bufs[conn] += chunk
            while b"\n" in bufs[conn]:
                line, bufs[conn] = bufs[conn].split(b"\n", 1)
                try:
                    reply = handle(role, pid, json.loads(line))
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
