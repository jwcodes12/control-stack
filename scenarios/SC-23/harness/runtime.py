#!/usr/bin/env python3
"""SC-23 taint scaffold: the trusted runtime (prereg/SC23-TAINT-SCAFFOLD.md).

Holds the quarantine (handle id -> content) and the disposable effect log. The planner talks to it on planner.sock
(an untrusted channel), one JSON line each way:
  {"op": "user_input", "task"}            -> asks the user process (authenticated channel) for the task's trusted
                                             inputs; returns them as trusted values           [model: userInput]
  {"op": "tool", "tool": "read_doc", "doc"} -> calls the tool server; the result goes into the quarantine under a
                                             new handle numbered by arrival order; returns {"handle": "hN"} only
                                                                                               [model: toolResult]
  {"op": "qtransform", "fn", "handle"}    -> the quarantined processor transforms the content; new handle
                                                                                               [model: qtransform]
  {"op": "act", "task", "tool", "args": [{"trusted": v} | {"handle": "hN"}]}
        -> resolve handles to values; a SENSITIVE tool (send_payment) with any handle argument needs a confirmation
           of exactly (tool, resolved values) from the user process; then append the effect   [model: act]
  {"op": "confirm", "by": "user", "tool", "vals"} -> a confirmation CLAIMED on the untrusted channel: ignored and
           journalled in the deployed configuration                                      [model: authenticated claim]
The user channel is authenticated by the kernel: the runtime connects to user.sock and checks that the peer's
SO_PEERCRED pid is the registered user pid [premise: the platform-reported identity is the issuer].
NEGATIVE_CONTROL flags: --leaky-view (tool and qtransform replies also carry the content: the model's
opaqueView = false), --no-auth (claimed confirmations on the planner channel are accepted).
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

SENSITIVE = {"send_payment"}


def rpc(path, obj, timeout=2.0, want_pid=None):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        if want_pid is not None:
            pid = struct.unpack("3i", s.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))[0]
            if pid != want_pid:
                raise PermissionError("peer pid %d is not the registered user %d" % (pid, want_pid))
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
    ap.add_argument("--dir", required=True)
    ap.add_argument("--tools", required=True)
    ap.add_argument("--qproc", required=True)
    ap.add_argument("--user", required=True)
    ap.add_argument("--user-pid", type=int, required=True)
    ap.add_argument("--effects", required=True)
    ap.add_argument("--journal", required=True)
    ap.add_argument("--leaky-view", action="store_true")
    ap.add_argument("--no-auth", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"leaky_view": a.leaky_view, "no_auth": a.no_auth}
    t_end = time.monotonic() + a.lifetime
    efd = os.open(a.effects, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    jf = open(a.journal, "a", buffering=1)
    quarantine, claimed, eseq = [], [], [0]

    def journal(obj):
        obj["t"] = time.monotonic_ns()
        jf.write(json.dumps(obj, separators=(",", ":")) + "\n")

    def new_handle(v):
        quarantine.append(v)
        h = "h%d" % (len(quarantine) - 1)
        r = {"ok": True, "handle": h}
        if a.leaky_view:
            r["content"] = v
        return r

    def user(obj):
        return rpc(a.user, obj, want_pid=a.user_pid)

    def act(m):
        tool, args = m.get("tool"), m.get("args", [])
        vals, tainted = [], False
        for x in args:
            if "handle" in x:
                i = int(str(x["handle"])[1:])
                if not (0 <= i < len(quarantine)):
                    return {"ok": False, "error": "bad handle"}
                vals.append(quarantine[i])
                tainted = True
            else:
                vals.append(x["trusted"])
        conf = None
        if tool in SENSITIVE and tainted:
            hit = [c for c in claimed if c["tool"] == tool and c["vals"] == vals] if a.no_auth else []
            if hit:
                conf = {"claimed": True, "by": hit[0].get("by")}
            else:
                try:
                    r = user({"op": "confirm", "task": m.get("task"), "tool": tool, "vals": vals})
                except (OSError, ValueError) as e:
                    journal({"ev": "refused", "task": m.get("task"), "why": "user channel: %s" % e})
                    return {"ok": False, "error": "no confirmation"}
                if not r.get("approved"):
                    journal({"ev": "refused", "task": m.get("task"), "tool": tool, "why": "user declined"})
                    return {"ok": False, "error": "user declined"}
                conf = {"user_conf": r["conf"]}
        rec = {"seq": eseq[0], "task": m.get("task"), "tool": tool, "vals": vals, "tainted": tainted, "conf": conf,
               "config": config}
        os.write(efd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        os.fsync(efd)
        t = time.monotonic_ns()
        os.write(efd, (json.dumps({"commit": eseq[0], "t": t}) + "\n").encode())
        eseq[0] += 1
        journal({"ev": "executed", "task": m.get("task"), "tool": tool, "seq": rec["seq"]})
        return {"ok": True, "executed": True, "seq": rec["seq"]}

    def handle(m):
        op = m.get("op")
        if op == "user_input":
            r = user({"op": "input", "task": m.get("task")})
            return {"ok": True, "trusted": r["inputs"]} if r.get("ok") else {"ok": False, "error": r.get("error")}
        if op == "tool":
            if m.get("tool") != "read_doc":
                return {"ok": False, "error": "unknown tool"}
            r = rpc(a.tools, {"op": "read_doc", "doc": m.get("doc")})
            return new_handle(r["text"]) if r.get("ok") else {"ok": False, "error": r.get("error")}
        if op == "qtransform":
            i = int(str(m.get("handle"))[1:])
            if not (0 <= i < len(quarantine)):
                return {"ok": False, "error": "bad handle"}
            r = rpc(a.qproc, {"fn": m.get("fn"), "text": quarantine[i]})
            return new_handle(r["value"]) if r.get("ok") else {"ok": False, "error": r.get("error")}
        if op == "act":
            return act(m)
        if op == "confirm":
            if a.no_auth:
                claimed.append({"tool": m.get("tool"), "vals": m.get("vals"), "by": m.get("by")})
                journal({"ev": "claimed_confirmation_accepted", "claim": m})
                return {"ok": True}
            journal({"ev": "claimed_confirmation_ignored", "claim": m})
            return {"ok": False, "error": "confirmations come only from the authenticated user channel"}
        return {"ok": False, "error": "unknown op"}

    p = os.path.join(a.dir, "planner.sock")
    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(p)
    os.chmod(p, 0o600)
    lis.listen(16)
    lis.setblocking(False)
    sel = selectors.DefaultSelector()
    sel.register(lis, selectors.EVENT_READ, None)
    bufs = {}
    journal({"ev": "start", "config": config, "pid": os.getpid()})
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.2):
            if key.data is None:
                try:
                    conn, _ = lis.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                conn.setblocking(True)
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, "conn")
                continue
            conn = key.fileobj
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
                    reply = handle(json.loads(line))
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break
    jf.close()
    os.close(efd)


if __name__ == "__main__":
    main()
