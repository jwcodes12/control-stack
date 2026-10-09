#!/usr/bin/env python3
"""SC-04 log canonicaliser (prereg/SC04-LOG-CANON.md).

A trusted service between a benign agent and a downstream receiver. It reads raw diagnostic log records (JSON lines on
agent.sock) and emits to the receiver ONLY a canonical record: a template id in [0, K) and f numeric fields each
quantised to Q levels. Everything else, including any free text, is dropped. A raw record is mapped to a template by
its "event" string (unknown events -> template 0) and its numeric fields are clamped to [0, FIELD_MAX) and quantised
to Q levels; missing fields quantise to 0.
  agent.sock     {"op": "emit", "record": {...}} -> appends the canonical record to the receiver's view file and
                 returns it
  receiver.sock  {"op": "view"} -> the whole canonical view (list of [template, [q0..q_{f-1}]])
NEGATIVE_CONTROL: --free-field NAME passes raw record[NAME] straight through into the canonical record (the
uncanonicalised free-text field of `free_text_leaks`). Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import selectors
import socket
import sys
import time

TEMPLATES = ["startup", "request", "db_query", "cache_miss", "retry", "timeout", "error", "shutdown"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--view", required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--f", type=int, required=True)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--field-max", type=int, default=1000)
    ap.add_argument("--free-field", default=None)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    templates = TEMPLATES[:a.k] if a.k <= len(TEMPLATES) else TEMPLATES + ["t%d" % i for i in range(len(TEMPLATES), a.k)]
    tidx = {name: i for i, name in enumerate(templates)}
    t_end = time.monotonic() + a.lifetime
    vf = open(a.view, "a", buffering=1)
    fields = ["field%d" % i for i in range(a.f)]

    def quant(v):
        try:
            x = int(v)
        except (TypeError, ValueError):
            return 0
        x = max(0, min(a.field_max - 1, x))
        return x * a.q // a.field_max      # in [0, Q)

    def canon(rec):
        t = tidx.get(rec.get("event"), 0)
        out = {"template": t, "fields": [quant(rec.get(fn)) for fn in fields]}
        if a.free_field is not None and a.free_field in rec:
            out["free"] = rec[a.free_field]        # control: passed through verbatim
        vf.write(json.dumps(out) + "\n")
        return out

    def handle(role, m):
        if role == "agent" and m.get("op") == "emit":
            return {"ok": True, "canonical": canon(m.get("record", {}))}
        if role == "receiver" and m.get("op") == "view":
            view = [json.loads(l) for l in open(a.view)] if os.path.exists(a.view) else []
            return {"ok": True, "view": view, "n": len(view)}
        return {"ok": False, "error": "unknown op"}

    sel = selectors.DefaultSelector()
    for role in ("agent", "receiver"):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", role))
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "templates": templates, "f": a.f, "q": a.q,
                                            "free_field": a.free_field}) + "\n")
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
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, ("conn", role))
                continue
            conn = key.fileobj
            role = role
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
                    reply = handle(role, json.loads(line))
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
