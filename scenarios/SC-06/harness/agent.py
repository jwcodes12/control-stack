#!/usr/bin/env python3
"""SC-06 shared artifacts: a scripted agent, A (writer) or B (reader/planner) (prereg/SC06-SHARED-ARTIFACTS.md).

Reads one JSON task per line on stdin and prints "DONE {task, result, state}" (state = this agent's planner context).
  write      {id, fields}            typed write (A includes a free-text "note"; the store decides what survives)
  write_raw  {id, text}              raw write attempt
  read       {id}                    B: read the typed view; every entry joins B's context
                                     (with --raw-read, NEGATIVE_CONTROL, B also reads A's raw file directly)
  act        {id, field, tool}       B: call a tool on the value of a context entry (by its store ctx_id)
B never acts on instructions found in text: it is a fixed script; what is inspected is only what reaches its context.
Self-contained.
"""
import argparse
import json
import os
import socket
import sys


def rpc(path, obj):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(10)
    try:
        s.connect(path)
        f = s.makefile("rwb")
        f.write((json.dumps(obj) + "\n").encode())
        f.flush()
        return json.loads(f.readline())
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", required=True)
    ap.add_argument("--store-dir", required=True)
    ap.add_argument("--raw-dir", required=True)
    ap.add_argument("--raw-read", action="store_true")
    a = ap.parse_args()
    sock = lambda r: os.path.join(a.store_dir, r + ".sock")
    state = []
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "name": a.name}) + "\n")
    sys.stdout.flush()
    for line in sys.stdin:
        t = json.loads(line)
        op, res = t["op"], None
        if op == "write":
            res = rpc(sock("typed"), {"op": "write", "id": t["id"], "fields": t["fields"]})
        elif op == "write_raw":
            res = rpc(sock("raw"), {"op": "write_raw", "id": t["id"], "text": t["text"]})
        elif op == "read":
            res = rpc(sock("read"), {"op": "read", "id": t["id"]})
            for e in res.get("entries", []):
                state.append({"ctx_id": e["ctx_id"], "artifact": e["artifact"], "field": e["field"],
                              "value": e["value"]})
            if a.raw_read:
                p = os.path.join(a.raw_dir, "%s.txt" % t["id"])
                if os.path.exists(p):
                    state.append({"artifact": t["id"], "field": "raw_file", "value": open(p).read()})
        elif op == "act":
            hit = [e for e in state if e.get("artifact") == str(t["id"]) and e["field"] == t["field"] and "ctx_id" in e]
            res = rpc(sock("act"), {"op": "act", "tool": t["tool"], "ctx_id": hit[-1]["ctx_id"]}) if hit \
                else {"ok": False, "error": "no such value in context"}
        sys.stdout.write("DONE " + json.dumps({"task": t, "result": res, "state": state}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
