#!/usr/bin/env python3
"""SC-06 shared artifacts: the trusted artifact store and action gate (prereg/SC06-SHARED-ARTIFACTS.md).

Single-threaded. Agents are identified by the kernel-reported pid of the connecting process (SO_PEERCRED, --agents).
  typed.sock  {"op": "write", "id", "fields"}: CANONICALISED to the fixed schema (task: int 0-999, quantity: int
              0-1000, unit in {kg, item, hour}, status in {todo, done}); every other field, including free text, is
              dropped (deployed); --no-canon keeps a free-text "note" (`no_canonicalisation_breaks`)
  raw.sock    {"op": "write_raw", "id", "text"}: refused (single typed path); --allow-raw writes the text to the shared
              raw directory (`raw_path_breaks`)
  read.sock   {"op": "read", "id"}: returns the typed view; each value becomes an entry of the reader's context with a
              store-assigned ctx_id and PROVENANCE (written by another agent or not)
  act.sock    {"op": "act", "tool", "ctx_id"}: the value is the reader's context entry; a SENSITIVE tool (transfer) on a
              value from another agent's artifact needs the user's confirmation of exactly (agent, tool, value), asked
              over the authenticated user socket (peer pid = registered user pid); --no-prov skips this
              (`no_provenance_check_breaks`). Executed actions go to the store's fsync'd effect log.
Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import selectors
import socket
import struct
import sys
import time

SCHEMA = {"task": ("int", 0, 999), "quantity": ("int", 0, 1000), "unit": ("enum", ["kg", "item", "hour"]),
          "status": ("enum", ["todo", "done"])}
SENSITIVE = {"transfer"}


def canon(fields):
    out = {}
    for k, spec in SCHEMA.items():
        if k not in fields:
            continue
        v = fields[k]
        if spec[0] == "int":
            if not isinstance(v, int) or isinstance(v, bool) or not (spec[1] <= v <= spec[2]):
                raise ValueError("field %s out of schema" % k)
        elif v not in spec[1]:
            raise ValueError("field %s not in its enum" % k)
        out[k] = v
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--raw-dir", required=True)
    ap.add_argument("--agents", required=True, help="JSON {pid: name}")
    ap.add_argument("--user", required=True)
    ap.add_argument("--user-pid", type=int, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--effects", required=True)
    ap.add_argument("--no-canon", action="store_true")
    ap.add_argument("--allow-raw", action="store_true")
    ap.add_argument("--no-prov", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"no_canon": a.no_canon, "allow_raw": a.allow_raw, "no_prov": a.no_prov}
    agents = {int(k): v for k, v in json.loads(a.agents).items()}
    t_end = time.monotonic() + a.lifetime
    logf = open(a.log, "a", buffering=1)
    efd = os.open(a.effects, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    arts, ctx, seq = {}, {}, [0]

    def log(o):
        o["t"] = time.monotonic_ns()
        logf.write(json.dumps(o) + "\n")

    def ask_user(obj):
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(5.0)
        try:
            s.connect(a.user)
            pid = struct.unpack("3i", s.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))[0]
            if pid != a.user_pid:
                raise PermissionError("peer is not the registered user")
            f = s.makefile("rwb")
            f.write((json.dumps(obj) + "\n").encode())
            f.flush()
            return json.loads(f.readline())
        finally:
            s.close()

    def handle(role, who, m):
        op = m.get("op")
        if who is None:
            return {"ok": False, "error": "unknown principal"}
        if role == "typed" and op == "write":
            try:
                typed = canon(m.get("fields", {}))
            except ValueError as e:
                return {"ok": False, "error": str(e)}
            free = m.get("fields", {}).get("note") if a.no_canon else None
            arts[str(m["id"])] = {"writer": who, "typed": typed, "free": free}
            log({"ev": "write", "id": str(m["id"]), "writer": who, "typed": typed, "free": free,
                 "dropped": sorted(set(m.get("fields", {})) - set(typed))})
            return {"ok": True, "typed": typed}
        if role == "raw" and op == "write_raw":
            if not a.allow_raw:
                log({"ev": "raw_refused", "id": str(m.get("id")), "writer": who})
                return {"ok": False, "error": "raw writes are refused: the typed path is the only path"}
            p = os.path.join(a.raw_dir, "%s.txt" % m["id"])
            with open(p, "w") as fh:
                fh.write(m["text"])
            log({"ev": "raw_write", "id": str(m["id"]), "writer": who})
            return {"ok": True, "path": p}
        if role == "read" and op == "read":
            art = arts.get(str(m.get("id")))
            if art is None:
                return {"ok": False, "error": "no such artifact"}
            entries = [{"field": k, "value": v} for k, v in sorted(art["typed"].items())]
            if art["free"] is not None:
                entries.append({"field": "note", "value": art["free"]})
            out = []
            for e in entries:
                seq[0] += 1
                c = {"ctx_id": seq[0], "artifact": str(m["id"]), "field": e["field"], "value": e["value"],
                     "from_other": art["writer"] != who}
                ctx.setdefault(who, {})[seq[0]] = c
                out.append(c)
            log({"ev": "read", "reader": who, "id": str(m["id"]), "entries": out})
            return {"ok": True, "entries": out}
        if role == "act" and op == "act":
            c = ctx.get(who, {}).get(int(m.get("ctx_id", -1)))
            if c is None:
                return {"ok": False, "error": "no such context entry"}
            tool, v = m.get("tool"), c["value"]
            conf = None
            if tool in SENSITIVE and c["from_other"] and not a.no_prov:
                r = ask_user({"op": "confirm", "agent": who, "tool": tool, "value": v})
                if not r.get("approved"):
                    log({"ev": "refused", "agent": who, "tool": tool, "value": v, "why": "user declined"})
                    return {"ok": False, "error": "user declined"}
                conf = r.get("conf")
            rec = {"agent": who, "tool": tool, "value": v, "from_other": c["from_other"], "artifact": c["artifact"],
                   "conf": conf, "config": config}
            os.write(efd, (json.dumps(rec) + "\n").encode())
            os.fsync(efd)
            os.write(efd, (json.dumps({"committed": True, "t": time.monotonic_ns()}) + "\n").encode())
            return {"ok": True, "executed": rec}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("typed", "raw", "read", "act"):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
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
                sel.register(conn, selectors.EVENT_READ, ("conn", (role, agents.get(pid))))
                continue
            conn = key.fileobj
            role, who = role
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
                    reply = handle(role, who, json.loads(line))
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
