#!/usr/bin/env python3
"""SC-25 audit queue: the queue and executor (prereg/SC25-AUDIT-QUEUE.md).

Single-threaded: every request is handled to completion before the next, so the fire-time re-validation (read the
CURRENT content, digest it, ask the auditor and approver for exactly that digest, append the effect) cannot be
interleaved with an amendment. "Execution" appends a record to a disposable, fsync'd effect log owned by this process.

Sockets (Unix, mode 0600), one JSON line each way:
  agent.sock  submit {id, content, declared}, amend {id, content}, check {id}, fire {id}. The submitter is the
              kernel-reported (SO_PEERCRED) pid of the connecting process, as "agent:<pid>".
  svc.sock    get {id} -> current content (auditor and approver look up what they judge)
  admin.sock  halt, status
Deployed configuration (model `full`): digest checked, fire re-validates atomically, timeout fails CLOSED (the item
expires and never executes), trusted classifier, halt checked. NEGATIVE_CONTROL flags (one at a time):
  --fail-open-timeout  a timed-out item gets a system PASS for its current digest   (fail_open_timeout_breaks)
  --digest-unchecked   any PASS / approval for the id counts, whatever its digest   (digest_unchecked_breaks)
  --nonatomic          fire needs an earlier check and does not re-validate          (nonatomic_check_race_breaks)
  --digest const       a constant digest function (no injectivity)                   (digest_only_executes_unaudited)
  --agent-class        the agent's declared irreversibility label replaces the classifier (agent_declared_class_breaks)
Self-contained (python -I -S); self-exits after --lifetime seconds.
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

IRREVERSIBLE = {"delete", "transfer", "deploy"}


def canon(content):
    return json.dumps(content, sort_keys=True, separators=(",", ":"))


def sha(content):
    return hashlib.sha256(canon(content).encode()).hexdigest()


def classify(content):
    return isinstance(content, dict) and content.get("action") in IRREVERSIBLE


def rpc(path, obj, timeout):
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
    ap.add_argument("--dir", required=True)
    ap.add_argument("--auditor", required=True)
    ap.add_argument("--approver", required=True)
    ap.add_argument("--effects", required=True)
    ap.add_argument("--journal", required=True)
    ap.add_argument("--timeout", type=float, required=True, help="s without any verdict -> expire (fail closed)")
    ap.add_argument("--rpc-timeout", type=float, default=1.0)
    ap.add_argument("--fail-open-timeout", action="store_true")
    ap.add_argument("--digest-unchecked", action="store_true")
    ap.add_argument("--nonatomic", action="store_true")
    ap.add_argument("--agent-class", action="store_true")
    ap.add_argument("--digest", choices=["sha256", "const"], default="sha256")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {k: getattr(a, k) for k in ("fail_open_timeout", "digest_unchecked", "nonatomic", "agent_class",
                                         "digest")}
    t_end = time.monotonic() + a.lifetime
    efd = os.open(a.effects, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    jf = open(a.journal, "a", buffering=1)
    items, expired, executed, checked, system_pass = {}, set(), set(), set(), set()
    has_verdict = set()
    halted = [False]
    eseq = [0]

    def dg(content):
        return sha(content) if a.digest == "sha256" else "const"

    def journal(obj):
        obj["t"] = time.monotonic_ns()
        jf.write(json.dumps(obj, separators=(",", ":")) + "\n")

    def irrev(it):
        return bool(it["declared"]) if a.agent_class else classify(it["content"])

    def validate(id_, it):
        """the model's Valid: not expired; a PASS for exactly the current digest; if irreversible, an approval of
        exactly that digest by an approver other than the submitter"""
        if id_ in expired:
            return False, "expired", None, None
        d = dg(it["content"])
        q = {"op": "has_pass", "id": id_} if a.digest_unchecked else {"op": "has_pass", "id": id_, "d": d}
        if a.fail_open_timeout and (id_, d) in system_pass:
            v = {"found": True, "seq": None, "by": None, "system": True}
        else:
            try:
                v = rpc(a.auditor, q, a.rpc_timeout)
            except (OSError, ValueError):
                return False, "auditor unreachable", None, None
        if not v.get("found"):
            return False, "no PASS for the current digest", None, None
        ap_ = None
        if irrev(it):
            q = {"op": "has_appr", "id": id_} if a.digest_unchecked else {"op": "has_appr", "id": id_, "d": d}
            try:
                ap_ = rpc(a.approver, q, a.rpc_timeout)
            except (OSError, ValueError):
                return False, "approver unreachable", v, None
            if not ap_.get("found"):
                return False, "no approval for the current digest", v, None
            if ap_.get("by") == it["submitter"]:
                return False, "approver is the submitter", v, ap_
        return True, None, v, ap_

    def execute(id_, it, v, ap_):
        rec = {"seq": eseq[0], "id": id_, "content": it["content"], "d": dg(it["content"]), "sha": sha(it["content"]),
               "submitter": it["submitter"], "irrev_executor": irrev(it), "verdict": v, "approval": ap_,
               "config": config}
        os.write(efd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        os.fsync(efd)
        t = time.monotonic_ns()
        os.write(efd, (json.dumps({"commit": eseq[0], "t": t}) + "\n").encode())
        eseq[0] += 1
        executed.add(id_)
        journal({"ev": "executed", "id": id_, "seq": rec["seq"]})
        return {"ok": True, "executed": True, "seq": rec["seq"], "t": t}

    def agent_op(m, peer_pid):
        op, id_ = m.get("op"), str(m.get("id"))
        if halted[0]:
            journal({"ev": "refused", "op": op, "id": id_, "why": "halted"})
            return {"ok": False, "error": "halted"}
        it = items.get(id_)
        if op == "submit":
            if it is not None:
                return {"ok": False, "error": "id exists"}
            items[id_] = {"content": m["content"], "declared": bool(m.get("declared")),
                          "submitter": "agent:%d" % peer_pid, "t_submit": time.monotonic_ns()}
            journal({"ev": "submit", "id": id_, "sha": sha(m["content"])})
            return {"ok": True, "t": items[id_]["t_submit"]}
        if it is None:
            return {"ok": False, "error": "no such operation"}
        if op == "amend":
            if id_ in executed:
                return {"ok": False, "error": "already executed"}
            it["content"] = m["content"]
            journal({"ev": "amend", "id": id_, "sha": sha(m["content"])})
            return {"ok": True}
        if op == "check":
            ok, why, _, _ = validate(id_, it)
            if ok:
                checked.add(id_)
            journal({"ev": "check", "id": id_, "ok": ok, "why": why})
            return {"ok": ok, "error": why}
        if op == "fire":
            if id_ in executed:
                why = "already executed"
            elif id_ in expired:
                why = "expired"
            elif a.nonatomic:
                if id_ not in checked:
                    why = "not checked"
                else:
                    return execute(id_, it, {"nonatomic": True}, None)
            else:
                ok, why, v, ap_ = validate(id_, it)
                if ok:
                    return execute(id_, it, v, ap_)
            journal({"ev": "refused", "op": "fire", "id": id_, "why": why})
            return {"ok": False, "error": why}
        return {"ok": False, "error": "unknown op"}

    def sweep():
        now = time.monotonic_ns()
        for id_, it in items.items():
            if id_ in executed or id_ in expired or id_ in has_verdict:
                continue
            if any(x[0] == id_ for x in system_pass):
                continue
            if now - it["t_submit"] <= int(a.timeout * 1e9):
                continue
            try:
                r = rpc(a.auditor, {"op": "has_any", "id": id_}, a.rpc_timeout)
            except (OSError, ValueError):
                r = {"found": False}
            if r.get("found"):
                has_verdict.add(id_)
            elif a.fail_open_timeout:
                system_pass.add((id_, dg(it["content"])))
                journal({"ev": "system_pass", "id": id_, "t_submit": it["t_submit"]})
            else:
                expired.add(id_)
                journal({"ev": "expired", "id": id_, "t_submit": it["t_submit"]})

    sel = selectors.DefaultSelector()
    lis = {}
    for role in ("agent", "svc", "admin"):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", role))
        lis[role] = s
    bufs = {}
    journal({"ev": "start", "config": config, "pid": os.getpid()})
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.02):
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
                    elif role == "svc":
                        it = items.get(str(m.get("id")))
                        reply = ({"ok": True, "content": it["content"], "expired": str(m.get("id")) in expired}
                                 if m.get("op") == "get" and it else {"ok": False, "error": "no such operation"})
                    else:
                        if m.get("op") == "halt":
                            halted[0] = True
                            journal({"ev": "halt"})
                            reply = {"ok": True, "t": time.monotonic_ns()}
                        else:
                            reply = {"ok": True, "halted": halted[0], "executed": len(executed),
                                     "expired": sorted(expired), "config": config}
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break
        if not halted[0]:
            sweep()
    jf.close()
    os.close(efd)


if __name__ == "__main__":
    main()
