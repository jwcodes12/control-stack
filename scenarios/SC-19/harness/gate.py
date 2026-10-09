#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: the gate (prereg/SC19-TWO-PHASE.md).

Single-threaded. Sockets (Unix, mode 0600), one JSON line each way:
  agent.sock     prepare {id, target, kind: "delete_all"}: records the op, its digest
                 sha256(canonical {id, target, kind, author}), and the affected count NOW; author = "agent:<pid>"
                 (SO_PEERCRED). commit {id, snap_id}.
  approver.sock  get_pending {id}, approve {id, digest}: only the registered approver pid; never the author
  admin.sock     halt, status
commit (deployed, model `full`) runs inside ONE `BEGIN IMMEDIATE` transaction on the production DB, so no other write
can interleave: not committed before; an approval of exactly the op digest by a non-author; the snapshot is VERIFIED
(asked of the verifier); it is FRESH (its recorded version of the target equals the target's current version); the
affected count, recomputed now, is <= R. Then the rows are deleted (dumped first to the gate's own deleted-rows file),
the version is bumped, a history row is written, and the transaction commits; then an fsync'd gate record.
NEGATIVE_CONTROL flags: --stale-ok (`stale_snapshot_breaks`), --unverified-ok (`unverified_snapshot_breaks`),
--prepare-count (`blast_radius_race_breaks`). Self-contained apart from dbutil.py.
"""
import argparse
import base64
import hashlib
import json
import os
import selectors
import socket
import struct
import sys
import time


def rpc(path, obj, timeout=10.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        return json.loads(f.readline())
    finally:
        s.close()


def op_digest(op):
    return hashlib.sha256(json.dumps({k: op[k] for k in ("id", "target", "kind", "author")}, sort_keys=True)
                          .encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--db", required=True)
    ap.add_argument("--dir", required=True)
    ap.add_argument("--verifier", required=True)
    ap.add_argument("--snapshot", required=True)
    ap.add_argument("--approver-pid", type=int, required=True)
    ap.add_argument("--R", type=int, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--deleted", required=True)
    ap.add_argument("--stale-ok", action="store_true")
    ap.add_argument("--unverified-ok", action="store_true")
    ap.add_argument("--prepare-count", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    sys.path.insert(0, a.lib)
    import dbutil
    config = {"stale_ok": a.stale_ok, "unverified_ok": a.unverified_ok, "prepare_count": a.prepare_count, "R": a.R}
    t_end = time.monotonic() + a.lifetime
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    dfd = os.open(a.deleted, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    pending, approvals, done, halted, seq = {}, {}, set(), [False], [0]

    def count(t):
        c = dbutil.connect(a.db)
        try:
            return c.execute("SELECT COUNT(*) FROM objs WHERE target=?", (t,)).fetchone()[0]
        finally:
            c.close()

    def commit(m):
        id_, sid = str(m.get("id")), m.get("snap_id")
        p = pending.get(id_)
        if p is None:
            return {"ok": False, "error": "no such operation"}
        if id_ in done:
            return {"ok": False, "error": "already committed"}
        ap_ = approvals.get(id_)
        if ap_ is None or ap_["digest"] != p["digest"] or ap_["approver"] == p["author"]:
            return {"ok": False, "error": "no approval of exactly this operation by another principal"}
        v = rpc(a.verifier, {"op": "verified", "snap_id": sid})
        if v.get("ok"):
            srec = v["rec"]
        elif a.unverified_ok:
            g = rpc(a.snapshot, {"op": "get", "snap_id": sid})
            if not g.get("ok"):
                return {"ok": False, "error": "no such snapshot"}
            srec = g["rec"]
        else:
            return {"ok": False, "error": "snapshot not verified"}
        t = p["target"]
        c = dbutil.connect(a.db)
        try:
            c.execute("BEGIN IMMEDIATE")
            cur = dbutil.version(c, t)
            snap_ver = srec["targets"].get(t, {}).get("ver")
            if not a.stale_ok and snap_ver != cur:
                c.execute("ROLLBACK")
                return {"ok": False, "error": "snapshot is not at the current version (%s != %s)" % (snap_ver, cur)}
            rows = dbutil.target_rows(c, t)
            n = p["count"] if a.prepare_count else len(rows)
            if n > a.R:
                c.execute("ROLLBACK")
                return {"ok": False, "error": "affected %d > R = %d" % (n, a.R)}
            for i, pl in rows:
                os.write(dfd, (json.dumps({"op": id_, "target": t, "id": i,
                                           "payload_b64": base64.b64encode(pl).decode()}) + "\n").encode())
            os.fsync(dfd)
            c.execute("DELETE FROM objs WHERE target=?", (t,))
            c.execute("INSERT OR REPLACE INTO versions(target, ver) VALUES (?, ?)", (t, cur + 1))
            c.execute("INSERT INTO history(target, ver_after, kind, rows_changed, rows_hash, t_ns) "
                      "VALUES (?,?,?,?,?,?)", (t, cur + 1, "destroy:" + id_, len(rows), dbutil.rows_hash(rows),
                                               time.monotonic_ns()))
            c.execute("COMMIT")
        except Exception:
            try:
                c.execute("ROLLBACK")
            except Exception:
                pass
            raise
        finally:
            c.close()
        done.add(id_)
        rec = {"seq": seq[0], "id": id_, "author": p["author"], "target": t, "ver_destroyed": cur, "actual": len(rows),
               "snap_id": sid, "snap_ver": snap_ver, "digest": p["digest"], "approval": ap_,
               "deleted_hash": dbutil.rows_hash(rows), "config": config}
        os.write(fd, (json.dumps(rec) + "\n").encode())
        os.fsync(fd)
        tc = time.monotonic_ns()
        os.write(fd, (json.dumps({"commit": seq[0], "t": tc}) + "\n").encode())
        seq[0] += 1
        return {"ok": True, "actual": len(rows), "ver_destroyed": cur, "t": tc}

    def handle(role, pid, m):
        op = m.get("op")
        if role == "admin":
            if op == "halt":
                halted[0] = True
                return {"ok": True, "t": time.monotonic_ns()}
            return {"ok": True, "halted": halted[0], "config": config}
        if halted[0]:
            return {"ok": False, "error": "halted"}
        if role == "agent":
            if op == "prepare":
                id_ = str(m["id"])
                if id_ in pending:
                    return {"ok": False, "error": "id exists"}
                p = {"id": id_, "target": m["target"], "kind": m.get("kind", "delete_all"), "author": "agent:%d" % pid}
                p["digest"] = op_digest(p)
                p["count"] = count(p["target"])
                pending[id_] = p
                return {"ok": True, "digest": p["digest"], "count": p["count"]}
            if op == "commit":
                return commit(m)
            return {"ok": False, "error": "unknown op"}
        if pid != a.approver_pid:
            return {"ok": False, "error": "not the approver"}
        p = pending.get(str(m.get("id")))
        if p is None:
            return {"ok": False, "error": "no such operation"}
        if op == "get_pending":
            return {"ok": True, "op": p}
        if op == "approve":
            me = "approver:%d" % pid
            if me == p["author"]:
                return {"ok": False, "error": "approver is the author"}
            approvals[p["id"]] = {"digest": m.get("digest"), "approver": me}
            return {"ok": True}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("agent", "approver", "admin"):
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
