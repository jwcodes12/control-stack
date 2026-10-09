#!/usr/bin/env python3
"""SC-27 anchor chain: independent reconciliation (prereg/SC27-ANCHOR-CHAIN.md).

Compares every manifest the verifier ACCEPTED (verifier's log) with the independent witness's own log: an accepted
head that the witness never anchored for that log is flagged (mirrors SC27Chain.AccOk / sc27_safe: every accepted
manifest is exactly an anchored log). Also extracts the witness's anchor and fork records.
Standalone:  python3 reconcile.py <verifier.jsonl> <witness.jsonl>
"""
import copy
import json
import os
import sys


def load_jsonl(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def witness_records(path):
    recs, commits = [], {}
    for r in load_jsonl(path):
        if "commit" in r and len(r) == 2:
            commits[r["commit"]] = r["t"]
        else:
            recs.append(r)
    for r in recs:
        r["t"] = commits.get(r["seq"])
    return recs


def reconcile(verdicts, witness):
    anchored = {(r["log"], r["head"]) for r in witness if r["kind"] == "anchor"}
    acc = [v for v in verdicts if v["accepted"]]
    bad = [{"log": v["log"], "head": v["head"][:16], "n": v["n"]} for v in acc if (v["log"], v["head"]) not in anchored]
    return {"accepted": len(acc), "rejected": len(verdicts) - len(acc), "accepted_unanchored": bad, "ok": not bad}


def mutation_selftest(verdicts, witness):
    acc = [v for v in verdicts if v["accepted"]]
    if not acc:
        return {"no accepted manifest to mutate": False}
    v = acc[0]
    w = [r for r in witness if not (r["kind"] == "anchor" and r["log"] == v["log"] and r["head"] == v["head"])]
    out = {"drop the anchor of an accepted head -> flagged": not reconcile(verdicts, w)["ok"]}
    vs = copy.deepcopy(verdicts) + [dict(v, head="0" * 64)]
    out["an accepted head nobody anchored -> flagged"] = not reconcile(vs, witness)["ok"]
    return out


if __name__ == "__main__":
    print(json.dumps(reconcile(load_jsonl(sys.argv[1]), witness_records(sys.argv[2])), indent=1))
