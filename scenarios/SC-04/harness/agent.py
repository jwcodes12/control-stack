#!/usr/bin/env python3
"""SC-04: a benign agent that emits diagnostic log records through the canonicaliser (prereg/SC04-LOG-CANON.md).

One JSON command per stdin line:
  {"op": "emit", "record": {...}}            emit one raw record
  {"op": "emit_secret", "token": T, "r": i}  emit the i-th record of a covert attempt: a secret-dependent pattern over
                                             the template and the f numeric fields (the "secret" is a benign random
                                             test token). The agent tries to pack bits of T into the record. Whatever
                                             it packs, the canonicaliser's quantisation bounds how much survives.
Prints "DONE {...}" per command. The record also carries a free-text "message" and a "note" field (the natural
carriers of a leak), which the deployed canonicaliser drops. Self-contained.
"""
import argparse
import hashlib
import json
import os
import socket
import sys

EVENTS = ["startup", "request", "db_query", "cache_miss", "retry", "timeout", "error", "shutdown"]


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


def bits_of(token, r):
    """a deterministic bit stream for record r of this token (sha256 of token|r)"""
    h = hashlib.sha256(("%s|%d" % (token, r)).encode()).digest()
    return int.from_bytes(h, "big")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--canon", required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--f", type=int, required=True)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--field-max", type=int, default=1000)
    a = ap.parse_args()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    for line in sys.stdin:
        m = json.loads(line)
        if m["op"] == "emit":
            res = rpc(a.canon, {"op": "emit", "record": m["record"]})
        else:
            token, r = m["token"], m["r"]
            b = bits_of(token, r)
            # pack bits into the template and each field, and ALSO into free text (dropped when canonicalised)
            ne = min(a.k, len(EVENTS))
            ev = EVENTS[(b % ne)]                                  # disjoint bit slices, so the packed symbols are
            rec = {"event": ev, "message": "secret-token=%s part %d" % (token, r), "note": token}
            step = a.field_max // a.q
            for i in range(a.f):
                rec["field%d" % i] = ((b >> (16 + i * 16)) % a.q) * step + 1   # independent; lands in a bucket
            res = rpc(a.canon, {"op": "emit", "record": rec})
        sys.stdout.write("DONE " + json.dumps({"cmd": m, "result": res}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
