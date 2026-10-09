#!/usr/bin/env python3
"""SC-09: independent reconciliation (prereg/SC09-ELEVATION-BROKER.md).

Reads the broker's own diff log and the CURRENT protected file. Mirrors SC09.sc09_safe / UseOk for this broker:
  rule_ok    every APPLIED change names a real rule, was invoked by the requester the rule names (by the PEER
             identity, not a claimed one), and its value is within the rule's range/enum
  replay     replaying the applied changes from the initial config reproduces the current file exactly (its sha256
             equals the last chain hash) - no out-of-band modification
  chain      the hash chain is linked (each applied entry's prev = the previous hash) and matches the file
RULES and the initial config are duplicated here (trusted), so the check does not rely on the broker's own rule code.
"""
import copy
import hashlib
import json
import os

RULES = {
    "set_threshold": {"field": "threshold", "kind": "range", "lo": 0, "hi": 100, "who": "ops"},
    "set_retries": {"field": "retries", "kind": "range", "lo": 0, "hi": 10, "who": "ops"},
    "set_mode": {"field": "mode", "kind": "enum", "values": ["safe", "normal"], "who": "ops"},
}
INIT = {"threshold": 50, "mode": "safe", "retries": 3}


def load(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def rule_ok(e):
    r = RULES.get(e.get("rule"))
    if r is None:
        return "no such rule"
    if e.get("peer") != r["who"]:
        return "applied by %r, not the rule's requester %r" % (e.get("peer"), r["who"])
    v = e.get("new")
    if r["kind"] == "range" and not (isinstance(v, int) and not isinstance(v, bool) and r["lo"] <= v <= r["hi"]):
        return "value %r out of range" % (v,)
    if r["kind"] == "enum" and v not in r["values"]:
        return "value %r not in enum" % (v,)
    if e.get("field") != r["field"]:
        return "field mismatch"
    return None


def reconcile(difflog, current_file):
    applied = [e for e in difflog if e.get("ev") == "applied"]
    defects = [{"seq": e["seq"], "why": w} for e in applied for w in [rule_ok(e)] if w]
    cur = copy.deepcopy(INIT)
    chain_ok, prev = True, hashlib.sha256(json.dumps(INIT, sort_keys=True).encode()).hexdigest()
    for e in applied:
        cur[e["field"]] = e["new"]
        if e.get("prev") != prev:
            chain_ok = False
        prev = e.get("sha256")
    actual = json.load(open(current_file))
    file_sha = hashlib.sha256(open(current_file, "rb").read()).hexdigest()
    replay_matches = cur == actual
    chain_matches_file = (prev == file_sha)
    return {"applied": len(applied), "refused": sum(1 for e in difflog if e.get("ev") == "refused"),
            "defects": defects, "replay_matches_file": replay_matches, "chain_linked": chain_ok,
            "chain_matches_file": chain_matches_file, "current": actual,
            "ok": not defects and replay_matches and chain_ok and chain_matches_file}


def mutation_selftest(difflog, current_file):
    out = {}
    applied = [e for e in difflog if e.get("ev") == "applied"]
    if applied:
        tgt = applied[0]
        dl = copy.deepcopy(difflog)
        for e in dl:
            if e.get("seq") == tgt["seq"]:
                e["peer"] = "guest"
        out["an applied change by a non-authorised requester -> flagged"] = not reconcile(dl, current_file)["ok"]
        dl = copy.deepcopy(difflog)
        for e in dl:
            if e.get("seq") == tgt["seq"]:
                e["new"] = "BOGUS-OUT-OF-SCHEMA"
        out["an applied value outside the rule's schema -> flagged"] = not reconcile(dl, current_file)["ok"]
        dl = copy.deepcopy(difflog)
        for e in dl:
            if e.get("seq") == tgt["seq"]:
                e["prev"] = "0" * 64
        out["a broken hash-chain link -> flagged"] = not reconcile(dl, current_file)["ok"]
    return out
