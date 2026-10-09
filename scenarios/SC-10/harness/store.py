#!/usr/bin/env python3
"""SC-10/11 policy store (prereg/SC10-POLICY-STORE.md).

Single-threaded. An append-only, versioned policy log: version = index; each record holds the policy value, its
SHA-256, the WRITER (the kernel-reported pid of the connecting process, SO_PEERCRED, mapped to "admin" for the
registered admin pid) and a CLOCK_MONOTONIC commit stamp taken after fsync.
  write.sock  {"op": "write", "policy": {...}}: only the admin pid (deployed); --any-writer is the NEGATIVE_CONTROL
              (`agent_writable_policy_breaks`)
  read.sock   {"op": "latest"} -> {version, policy, digest, length, t_answer}: answered atomically by the store
Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import json
import os
import selectors
import socket
import struct
import sys
import time


def digest(p):
    return hashlib.sha256(json.dumps(p, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--admin-pid", type=int, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--any-writer", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    t_end = time.monotonic() + a.lifetime
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    versions = []

    def handle(role, pid, m):
        op = m.get("op")
        if role == "write" and op == "write":
            who = "admin" if pid == a.admin_pid else "pid:%d" % pid
            if who != "admin" and not a.any_writer:
                return {"ok": False, "error": "only the admin may write policy"}
            rec = {"version": len(versions), "policy": m["policy"], "digest": digest(m["policy"]), "writer": who}
            os.write(fd, (json.dumps(rec) + "\n").encode())
            os.fsync(fd)
            rec["t_commit"] = time.monotonic_ns()
            os.write(fd, (json.dumps({"commit": rec["version"], "t": rec["t_commit"]}) + "\n").encode())
            versions.append(rec)
            return {"ok": True, "version": rec["version"], "t_commit": rec["t_commit"]}
        if role == "read" and op == "latest":
            if not versions:
                return {"ok": False, "error": "no policy"}
            v = versions[-1]
            return {"ok": True, "version": v["version"], "policy": v["policy"], "digest": v["digest"],
                    "length": len(versions), "t_answer": time.monotonic_ns()}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("write", "read"):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", role))
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "any_writer": a.any_writer}) + "\n")
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
