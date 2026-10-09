#!/usr/bin/env python3
"""SC-23 taint scaffold: independent reconciliation (prereg/SC23-TAINT-SCAFFOLD.md).

Reads only the runtime's effect log and the USER process's own log (records each followed by a
{"commit": seq, "t": ns} line written after fsync). It never uses the runtime's own taint flag or confirmation
reference. For every effect of a sensitive tool (send_payment) it requires one of:
  confirmed : a user confirm record for the same task with approved = true, the same tool and EXACTLY the same
              values, committed before the effect     (SC23IsolationV2.ActOk / sc23v2_safe_authenticated)
  user-only : every value is one of the trusted inputs the user gave for that task (logged before the effect)
Anything else is a sensitive action on values the user neither supplied nor confirmed: the laundering and forged-
confirmation outcomes of `leaky_view_launders` and `forged_confirmation_without_auth`.
Standalone:  python3 reconcile.py <effects.jsonl> <user.jsonl>
"""
import copy
import json
import sys

SENSITIVE = {"send_payment"}


def load(path):
    recs, commits = [], {}
    try:
        fh = open(path)
    except FileNotFoundError:
        return []
    with fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if "commit" in r:
                commits[r["commit"]] = r["t"]
            else:
                recs.append(r)
    for r in recs:
        r["t"] = commits.get(r["seq"])
    return recs


def reconcile(effects, user):
    bad, kinds = [], {}
    for e in effects:
        if e["tool"] not in SENSITIVE:
            continue
        if e["t"] is None:
            bad.append({"task": e["task"], "vals": e["vals"], "why": "uncommitted effect"})
            continue
        conf = any(r["kind"] == "confirm" and r.get("approved") is True and r["task"] == e["task"] and
                   r["tool"] == e["tool"] and r["vals"] == e["vals"] and r["t"] is not None and r["t"] < e["t"]
                   for r in user)
        inputs = set()
        for r in user:
            if r["kind"] == "input" and r["task"] == e["task"] and r["t"] is not None and r["t"] < e["t"]:
                inputs |= {json.dumps(v) for v in r["inputs"].values()}
        user_only = all(json.dumps(v) in inputs for v in e["vals"])
        k = "confirmed" if conf else "user-only" if user_only else "VIOLATION"
        kinds[k] = kinds.get(k, 0) + 1
        if k == "VIOLATION":
            bad.append({"task": e["task"], "tool": e["tool"], "vals": e["vals"],
                        "why": "sensitive action on values the user neither supplied nor confirmed"})
    sens = [e for e in effects if e["tool"] in SENSITIVE]
    return {"effects": len(effects), "sensitive": len(sens), "kinds": kinds, "violations": bad, "ok": not bad}


def mutation_selftest(effects, user):
    out = {}
    sens = [e for e in effects if e["tool"] in SENSITIVE]
    if not sens:
        return {"no sensitive effect to mutate": False}
    e = sens[0]
    flagged = lambda ef, us: any(v["task"] == e["task"] for v in reconcile(ef, us)["violations"])
    out["drop the user's confirmation -> violation"] = flagged(
        effects, [r for r in user if not (r["kind"] == "confirm" and r["task"] == e["task"])])
    ef = copy.deepcopy(effects)
    for x in ef:
        if x["seq"] == e["seq"]:
            x["vals"] = [999, 7]
    out["change the executed values -> violation"] = flagged(ef, user)
    us = copy.deepcopy(user)
    for r in us:
        if r["kind"] == "confirm" and r["task"] == e["task"]:
            r["t"] = e["t"] + 1
    out["confirmation committed after the effect -> violation"] = flagged(effects, us)
    us = copy.deepcopy(user)
    for r in us:
        if r["kind"] == "confirm" and r["task"] == e["task"]:
            r["approved"] = False
    out["confirmation declined -> violation"] = flagged(effects, us)
    return out


if __name__ == "__main__":
    r = reconcile(load(sys.argv[1]), load(sys.argv[2]))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r["ok"] else 1)
