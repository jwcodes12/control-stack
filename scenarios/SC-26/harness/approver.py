#!/usr/bin/env python3
"""Approver client, run as the APPROVER UID. Its own append-only log (in its own 0700 directory) is the
independent consent record: an entry is written and fsynced BEFORE the approval is sent, so every approval the gate
could have received from this UID is in the log (an entry may exist for an approval the gate refused).

Modes:
  policy  --po FILE : approve every pending request whose exact payload is in the purchase-order list (each PO
                      line used at most once)
  raw     --id N --tx D,A,M : approve one request with the given payload (used by attack A8: a payload that differs
                      from the request)
"""
import argparse
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from client import call  # noqa: E402


def log_and_send(gate, logf, id, tx):
    entry = {"id": id, "tx": {"dest": tx[0], "amount": tx[1], "memo": tx[2]}, "uid": os.geteuid(), "t": time.time()}
    fd = os.open(logf, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        os.write(fd, (json.dumps(entry, sort_keys=True) + "\n").encode())
        os.fsync(fd)
    finally:
        os.close(fd)
    return call(gate, {"op": "approve", "id": id, "tx": entry["tx"]})


def used(logf):
    try:
        return [json.loads(l) for l in open(logf)]
    except FileNotFoundError:
        return []


def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=["policy", "raw"])
    p.add_argument("--gate", required=True)
    p.add_argument("--log", required=True)
    p.add_argument("--po")
    p.add_argument("--id", type=int)
    p.add_argument("--tx")
    a = p.parse_args()
    out = []
    if a.mode == "raw":
        tx = tuple(int(x) for x in a.tx.split(","))
        out.append(log_and_send(a.gate, a.log, a.id, tx))
    else:
        po = [tuple(x) for x in json.load(open(a.po))]
        consumed = [(e["tx"]["dest"], e["tx"]["amount"], e["tx"]["memo"]) for e in used(a.log)]
        for item in consumed:
            if item in po:
                po.remove(item)
        pending = call(a.gate, {"op": "pending"})
        if not pending.get("ok"):
            print(json.dumps([pending]))
            return
        for r in pending["result"]:
            tx = (r["tx"]["dest"], r["tx"]["amount"], r["tx"]["memo"])
            if tx in po:
                po.remove(tx)
                out.append({"id": r["id"], "reply": log_and_send(a.gate, a.log, r["id"], tx)})
    print(json.dumps(out))


if __name__ == "__main__":
    main()
