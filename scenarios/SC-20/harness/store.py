#!/usr/bin/env python3
"""SC-20 data provenance: the example store, registry and freezer (prereg/SC20-DATA-PROVENANCE.md).

Single-threaded. Examples are JSON files <store>/examples/<id>.json (mutable storage, as in the model, where stored
contents can be edited); the digest is SHA-256 of canonical JSON. Sockets (mode 0600), one JSON line each way:
  ingest.sock  {id, content} from a SOURCE process; the source is named by its kernel-reported pid (--sources map).
               The example is stored with that source and the digest registered for it at ingestion.
  agent.sock   {id, content}: an agent-written example (no source; writer = "pid:<peer pid>"): QUARANTINED
  review.sock  get {id}; promote {id, digest}: only the registered reviewer pid, never the example's writer, only
               quarantined examples, and only for the CURRENT digest
  admin.sock   freeze {ids}: the manifest is the admitted examples' (id, current digest); written fsync'd to the
               manifest file. Admitted: from an ALLOWLISTED source with registered digest == current digest, or
               quarantined and promoted for exactly the current digest.
NEGATIVE_CONTROL flags: --no-quarantine (`no_quarantine_breaks`), --no-source-check (`unlisted_source_breaks`).
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


def digest(content):
    return hashlib.sha256(json.dumps(content, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--store", required=True)
    ap.add_argument("--sources", required=True, help="JSON {pid: source name}")
    ap.add_argument("--allow", required=True, help="comma list of allowlisted source names")
    ap.add_argument("--reviewer-pid", type=int, required=True)
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--no-quarantine", action="store_true")
    ap.add_argument("--no-source-check", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"no_quarantine": a.no_quarantine, "no_source_check": a.no_source_check}
    sources = {int(k): v for k, v in json.loads(a.sources).items()}
    allow = set(x for x in a.allow.split(",") if x)
    ex_dir = os.path.join(a.store, "examples")
    os.makedirs(ex_dir, mode=0o700, exist_ok=True)
    meta, promoted = {}, {}
    t_end = time.monotonic() + a.lifetime
    logf = open(a.log, "a", buffering=1)

    def log(obj):
        obj["t"] = time.monotonic_ns()
        logf.write(json.dumps(obj) + "\n")

    def path(id_):
        return os.path.join(ex_dir, "%s.json" % id_)

    def put(id_, content):
        tmp = path(id_) + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(content, fh, sort_keys=True)
            fh.flush()
            os.fsync(fh.fileno())
        os.rename(tmp, path(id_))

    def current(id_):
        try:
            return json.load(open(path(id_)))
        except (OSError, ValueError):
            return None

    def admitted(id_):
        m, c = meta.get(id_), current(id_)
        if m is None or c is None:
            return False, "no such example"
        d = digest(c)
        if m["src"] is not None:
            if a.no_source_check:
                return True, "source check disabled"
            if m["src"] not in allow:
                return False, "source %s not allowlisted" % m["src"]
            return (m["registered"] == d), ("registered" if m["registered"] == d else "content differs from registration")
        if a.no_quarantine:
            return True, "quarantine disabled"
        return (promoted.get(id_) == d), ("promoted" if promoted.get(id_) == d else "quarantined, not promoted")

    def handle(role, pid, m):
        op, id_ = m.get("op"), str(m.get("id"))
        if role == "ingest":
            src = sources.get(pid, "unknown:%d" % pid)
            if id_ in meta:
                return {"ok": False, "error": "id exists"}
            put(id_, m["content"])
            meta[id_] = {"src": src, "writer": src, "registered": digest(m["content"])}
            log({"ev": "ingest", "id": id_, "src": src, "digest": meta[id_]["registered"]})
            return {"ok": True}
        if role == "agent":
            if id_ in meta:
                return {"ok": False, "error": "id exists"}
            put(id_, m["content"])
            meta[id_] = {"src": None, "writer": "pid:%d" % pid, "registered": None}
            log({"ev": "agent_write", "id": id_, "writer": "pid:%d" % pid, "digest": digest(m["content"])})
            return {"ok": True, "quarantined": not a.no_quarantine}
        if role == "review":
            if pid != a.reviewer_pid:
                return {"ok": False, "error": "not the reviewer"}
            mt, c = meta.get(id_), current(id_)
            if mt is None or c is None:
                return {"ok": False, "error": "no such example"}
            if op == "get":
                return {"ok": True, "content": c, "writer": mt["writer"], "src": mt["src"], "digest": digest(c)}
            if op == "promote":
                if mt["writer"] == "pid:%d" % pid:
                    return {"ok": False, "error": "reviewer is the writer"}
                if mt["src"] is not None:
                    return {"ok": False, "error": "not a quarantined example"}
                if m.get("digest") != digest(c):
                    return {"ok": False, "error": "digest is not the current content's"}
                promoted[id_] = m["digest"]
                log({"ev": "promote", "id": id_, "digest": m["digest"], "reviewer": "pid:%d" % pid})
                return {"ok": True}
        if role == "admin" and op == "freeze":
            manifest, excluded = [], {}
            for i in m["ids"]:
                ok, why = admitted(str(i))
                if ok:
                    manifest.append([str(i), digest(current(str(i)))])
                else:
                    excluded[str(i)] = why
            tmp = a.manifest + ".tmp"
            with open(tmp, "w") as fh:
                json.dump({"manifest": manifest, "config": config}, fh)
                fh.flush()
                os.fsync(fh.fileno())
            os.rename(tmp, a.manifest)
            log({"ev": "freeze", "n": len(manifest), "excluded": excluded})
            return {"ok": True, "n": len(manifest), "excluded": excluded}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("ingest", "agent", "review", "admin"):
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
                sel.register(conn, selectors.EVENT_READ, ("conn", (role, pid)))
                continue
            conn = key.fileobj
            role, pid = role
            try:
                chunk = conn.recv(1 << 20)
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
