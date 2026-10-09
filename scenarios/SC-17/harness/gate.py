#!/usr/bin/env python3
"""SC-17 drift reconcile: the apply gate, owner of the DESIRED grant set (prereg/SC17-DRIFT-RECONCILE.md).

Single-threaded (each request completes before the next). Sockets (Unix, mode 0600), one JSON line each way:
  agent.sock     propose {id, diff: {adds, dels}}, amend {id, diff} (author only), apply {id}
                 (author = "agent:<pid>" from SO_PEERCRED)
  reviewer.sock  get_proposal {id}, approve {id, diff}: only the registered reviewer pid; the approval records
                 exactly the diff the reviewer sent, and a reviewer may not approve its own proposal
  read.sock      get_desired -> {desired, version}
apply (deployed, model `full`): not applied before; an approval exists whose diff EQUALS the current diff (`exact`);
the ceiling holds on the RESULTING desired state (`resultCheck`); then desired := result, version += 1, the new
desired state is pushed to the cluster's trusted socket (which reverts any drift: `drift`), and an fsync'd apply
record is written. The ceiling forbids any subject holding both [s, "read", "secrets"] and [s, "exec", "prod"].
NEGATIVE_CONTROL flag: --text-ceiling checks the ceiling on the diff's adds only (`text_ceiling_composition_breaks`).
Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import selectors
import socket
import struct
import sys
import time


def forbidden(grants):
    gs = {tuple(g) for g in grants}
    return sorted({s for (s, v, r) in gs if (s, "read", "secrets") in gs and (s, "exec", "prod") in gs})


def apply_diff(state, diff):
    dels = {tuple(g) for g in diff.get("dels", [])}
    out = [tuple(g) for g in state if tuple(g) not in dels]
    for g in diff.get("adds", []):
        if tuple(g) not in out:
            out.append(tuple(g))
    return sorted(out)


def rpc(path, obj, timeout=2.0):
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
    ap.add_argument("--dir", required=True)
    ap.add_argument("--init", required=True)
    ap.add_argument("--cluster-ctl", required=True)
    ap.add_argument("--reviewer-pid", type=int, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--text-ceiling", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"text_ceiling": a.text_ceiling}
    t_end = time.monotonic() + a.lifetime
    desired = sorted(tuple(g) for g in json.load(open(a.init)))
    version, props, approvals, done, seq = [0], {}, {}, set(), [0]
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)

    def record(rec):
        rec["seq"] = seq[0]
        seq[0] += 1
        os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        os.fsync(fd)
        t = time.monotonic_ns()
        os.write(fd, (json.dumps({"commit": rec["seq"], "t": t}) + "\n").encode())
        return t

    def agent_op(m, pid):
        nonlocal desired
        op, id_ = m.get("op"), str(m.get("id"))
        me = "agent:%d" % pid
        if op == "propose":
            if id_ in props:
                return {"ok": False, "error": "id exists"}
            props[id_] = {"author": me, "diff": m["diff"]}
            return {"ok": True}
        p = props.get(id_)
        if p is None:
            return {"ok": False, "error": "no such proposal"}
        if op == "amend":
            if p["author"] != me:
                return {"ok": False, "error": "only the author amends"}
            p["diff"] = m["diff"]
            return {"ok": True}
        if op == "apply":
            if id_ in done:
                return {"ok": False, "error": "already applied"}
            ap_ = approvals.get(id_)
            if ap_ is None or ap_["diff"] != p["diff"]:
                return {"ok": False, "error": "no approval of exactly the current diff"}
            result = apply_diff(desired, p["diff"])
            bad = forbidden(p["diff"].get("adds", [])) if a.text_ceiling else forbidden(result)
            if bad:
                return {"ok": False, "error": "ceiling: forbidden combination for %s" % bad}
            desired = result
            version[0] += 1
            done.add(id_)
            try:
                push = rpc(a.cluster_ctl, {"op": "set_state", "grants": [list(g) for g in desired],
                                           "version": version[0], "by": "gate"})
            except (OSError, ValueError) as e:
                push = {"ok": False, "error": str(e)}
            t = record({"id": id_, "author": p["author"], "diff": p["diff"], "approval": ap_,
                        "desired": [list(g) for g in desired], "version": version[0], "push": push,
                        "config": config})
            return {"ok": True, "version": version[0], "t": t}
        return {"ok": False, "error": "unknown op"}

    def reviewer_op(m, pid):
        if pid != a.reviewer_pid:
            return {"ok": False, "error": "not the reviewer"}
        id_ = str(m.get("id"))
        p = props.get(id_)
        if p is None:
            return {"ok": False, "error": "no such proposal"}
        if m.get("op") == "get_proposal":
            return {"ok": True, "author": p["author"], "diff": p["diff"]}
        if m.get("op") == "approve":
            if p["author"] == "reviewer:%d" % pid:
                return {"ok": False, "error": "reviewer is the author"}
            approvals[id_] = {"reviewer": "reviewer:%d" % pid, "diff": m["diff"], "author": p["author"]}
            return {"ok": True}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("agent", "reviewer", "read"):
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
                    m = json.loads(line)
                    if role == "agent":
                        reply = agent_op(m, pid)
                    elif role == "reviewer":
                        reply = reviewer_op(m, pid)
                    else:
                        reply = {"ok": True, "desired": [list(g) for g in desired], "version": version[0]}
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
