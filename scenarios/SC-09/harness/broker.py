#!/usr/bin/env python3
"""SC-09 exact-argument elevation broker (prereg/SC09-ELEVATION-BROKER.md).

UNPRIVILEGED: the broker and requesters are ordinary processes under ONE UID. The broker identifies a caller by the
kernel-reported PID of the connecting process (SO_PEERCRED), mapped to a requester NAME via --requesters. This tests
the exact-argument rule check and the refusal to trust a claimed caller field. It does NOT test UID-level privilege
separation (see the prereg).

The broker owns a protected JSON config file in its private 0700 directory inside the run dir. A requester never
receives a handle to the file; it can only ask the broker to apply a preregistered (command, exact-argument) rule.
Rules (name: field, allowed range/enum): set_threshold 0-100, set_retries 0-10, set_mode in {safe, normal}; each rule
also names which requester NAME may invoke it. On every applied change the broker appends to its own fsync'd diff log
{field, old, new, caller, rule, sha256 of the whole file after} and advances a hash chain.
  {"op": "apply", "rule", "value"}            apply a rule as the PEER identity
  {"op": "apply", "rule", "value", "as": N}   a deputy request claiming to act as requester N
  {"op": "read_resource"}                     the current config (read-only view; still no file handle)
NEGATIVE_CONTROL flags:
  --no-arg-check   rules apply with ANY value (the unrestricted-elevation rule)      (unrestricted_elevation_breaks)
  --trust-claimed  authorise by the claimed "as" field instead of the peer identity  (confused_deputy_breaks)
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

RULES = {
    "set_threshold": {"field": "threshold", "kind": "range", "lo": 0, "hi": 100, "who": "ops"},
    "set_retries": {"field": "retries", "kind": "range", "lo": 0, "hi": 10, "who": "ops"},
    "set_mode": {"field": "mode", "kind": "enum", "values": ["safe", "normal"], "who": "ops"},
}
INIT = {"threshold": 50, "mode": "safe", "retries": 3}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--priv", required=True, help="the broker's private 0700 dir")
    ap.add_argument("--requesters", required=True, help="JSON {pid: name}")
    ap.add_argument("--difflog", required=True)
    ap.add_argument("--no-arg-check", action="store_true")
    ap.add_argument("--trust-claimed", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"no_arg_check": a.no_arg_check, "trust_claimed": a.trust_claimed}
    requesters = {int(k): v for k, v in json.loads(a.requesters).items()}
    os.makedirs(a.priv, mode=0o700, exist_ok=True)
    os.chmod(a.priv, 0o700)
    resource = os.path.join(a.priv, "config.json")
    with open(resource, "w") as fh:
        json.dump(INIT, fh, sort_keys=True)
    os.chmod(resource, 0o600)
    t_end = time.monotonic() + a.lifetime
    dfd = os.open(a.difflog, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    chain = [hashlib.sha256(open(resource, "rb").read()).hexdigest()]
    seq = [0]

    def log(rec):
        rec["seq"] = seq[0]
        seq[0] += 1
        os.write(dfd, (json.dumps(rec) + "\n").encode())
        os.fsync(dfd)
        return rec

    def apply(caller, m):
        rule = RULES.get(m.get("rule"))
        if rule is None:
            return {"ok": False, "error": "no such rule"}
        actor = m["as"] if (a.trust_claimed and "as" in m) else caller   # deployed: always the peer identity
        if actor != rule["who"]:
            log({"ev": "refused", "rule": m.get("rule"), "why": "caller %r may not invoke this rule" % actor,
                 "peer": caller, "claimed": m.get("as")})
            return {"ok": False, "error": "caller may not invoke this rule"}
        v = m.get("value")
        if not a.no_arg_check:
            if rule["kind"] == "range" and not (isinstance(v, int) and not isinstance(v, bool) and
                                                rule["lo"] <= v <= rule["hi"]):
                log({"ev": "refused", "rule": m["rule"], "why": "argument out of range", "value": v, "peer": caller})
                return {"ok": False, "error": "argument out of the rule's range"}
            if rule["kind"] == "enum" and v not in rule["values"]:
                log({"ev": "refused", "rule": m["rule"], "why": "argument not in enum", "value": v, "peer": caller})
                return {"ok": False, "error": "argument not in the rule's enum"}
        cur = json.load(open(resource))
        old = cur.get(rule["field"])
        cur[rule["field"]] = v
        tmp = resource + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(cur, fh, sort_keys=True)
            fh.flush()
            os.fsync(fh.fileno())
        os.rename(tmp, resource)
        h = hashlib.sha256(open(resource, "rb").read()).hexdigest()
        chain.append(h)
        log({"ev": "applied", "rule": m["rule"], "field": rule["field"], "old": old, "new": v, "caller": caller,
             "peer": caller, "claimed": m.get("as"), "sha256": h, "prev": chain[-2], "config": config,
             "t": time.monotonic_ns()})
        return {"ok": True, "field": rule["field"], "value": v}

    def handle(caller, m):
        if caller is None:
            return {"ok": False, "error": "unknown caller"}
        if m.get("op") == "apply":
            return apply(caller, m)
        if m.get("op") == "read_resource":
            return {"ok": True, "config": json.load(open(resource))}
        return {"ok": False, "error": "unknown op"}

    p = os.path.join(a.dir, "broker.sock")
    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(p)
    os.chmod(p, 0o600)
    lis.listen(32)
    lis.setblocking(False)
    sel = selectors.DefaultSelector()
    sel.register(lis, selectors.EVENT_READ, None)
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config, "resource_sha0": chain[0]}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.2):
            if key.data is None:
                try:
                    conn, _ = lis.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                conn.setblocking(True)
                pid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED,
                                                          struct.calcsize("3i")))[0]
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, ("conn", requesters.get(pid)))
                continue
            conn = key.fileobj
            _, caller = key.data
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
                    reply = handle(caller, json.loads(line))
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
