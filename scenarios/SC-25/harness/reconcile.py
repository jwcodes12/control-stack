#!/usr/bin/env python3
"""SC-25 audit queue: independent reconciliation (prereg/SC25-AUDIT-QUEUE.md).

Reads only the executor's effect log and the auditor's and approver's OWN logs. Each log is a sequence of records,
each followed by a {"commit": seq, "t": ns} line written after fsync. For every effect-log entry e it requires,
mirroring `SC25.ExecOk` / `SC25.Good` and, at content level, `SC25Content.sc25_content_safe`:
  audited   : an auditor record with the same id, pass = true, and EXACTLY the executed content (SHA-256 of the
              canonical JSON of the content the auditor saw equals that of e's content), committed before e
  approved  : if the trusted classifier calls e's content irreversible, an approver record with the same id and
              exactly that content, by a principal other than e's submitter, committed before e
  once      : no id executed twice
The digest the executor used (which may be weak in a control) is never trusted: matching is on full content.
Standalone:  python3 reconcile.py <effects.jsonl> <auditor.jsonl> <approver.jsonl>
"""
import copy
import hashlib
import json
import sys

IRREVERSIBLE = {"delete", "transfer", "deploy"}


def canon(content):
    return json.dumps(content, sort_keys=True, separators=(",", ":"))


def sha(content):
    return hashlib.sha256(canon(content).encode()).hexdigest()


def classify(content):
    return isinstance(content, dict) and content.get("action") in IRREVERSIBLE


def load(path):
    """records with their commit time (records without a commit line get t = None: not committed)"""
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


def reconcile(effects, audits, approvals):
    bad = {"unaudited": [], "unapproved": [], "uncommitted_effect": [], "dup": []}
    seen = set()
    for e in effects:
        if e["t"] is None:
            bad["uncommitted_effect"].append(e["id"])
            continue
        if e["id"] in seen:
            bad["dup"].append(e["id"])
        seen.add(e["id"])
        h = sha(e["content"])
        ok_a = any(r["id"] == e["id"] and r.get("pass") is True and sha(r["content"]) == h and r["t"] is not None
                   and r["t"] < e["t"] for r in audits)
        if not ok_a:
            bad["unaudited"].append({"id": e["id"], "content": e["content"],
                                     "auditor_records": [{"pass": r.get("pass"), "sha": sha(r["content"])[:12]}
                                                         for r in audits if r["id"] == e["id"]]})
        if classify(e["content"]):
            ok_p = any(r["id"] == e["id"] and sha(r["content"]) == h and r["by"] != e["submitter"] and
                       r["t"] is not None and r["t"] < e["t"] for r in approvals)
            if not ok_p:
                bad["unapproved"].append({"id": e["id"], "content": e["content"]})
    res = {"effects": len(effects), "audit_records": len(audits), "approval_records": len(approvals),
           "executed_ids": sorted(seen)}
    res.update(bad)
    res["ok"] = not any(bad.values())
    res["flagged_ids"] = sorted({x if isinstance(x, str) else x["id"] for v in bad.values() for x in v})
    return res


def mutation_selftest(effects, audits, approvals):
    """each entry True iff reconciliation flags the single defect injected into a copy of the stored logs"""
    out = {}
    if not effects:
        return {"no effect to mutate": False}
    e = effects[len(effects) // 2]
    out["drop the auditor record of one executed op -> unaudited"] = e["id"] in reconcile(
        effects, [r for r in audits if r["id"] != e["id"]], approvals)["flagged_ids"]
    ef = copy.deepcopy(effects)
    for x in ef:
        if x["id"] == e["id"]:
            x["content"] = dict(x["content"], note=str(x["content"].get("note", "")) + " amended")
    out["change one executed content after its audit -> unaudited"] = e["id"] in reconcile(
        ef, audits, approvals)["flagged_ids"]
    au = copy.deepcopy(audits)
    for r in au:
        if r["id"] == e["id"]:
            r["t"] = e["t"] + 1
    out["audit committed after the execution -> unaudited"] = e["id"] in reconcile(effects, au, approvals)["flagged_ids"]
    ef2 = copy.deepcopy(effects) + [dict(e, seq=10 ** 6, t=e["t"] + 1)]
    out["execute one id twice -> dup"] = reconcile(ef2, audits, approvals)["dup"] == [e["id"]]
    irr = [x for x in effects if classify(x["content"])]
    if irr:
        x = irr[0]
        out["drop the approval of one irreversible op -> unapproved"] = x["id"] in reconcile(
            effects, audits, [r for r in approvals if r["id"] != x["id"]])["flagged_ids"]
        ap = copy.deepcopy(approvals)
        for r in ap:
            if r["id"] == x["id"]:
                r["by"] = x["submitter"]
        out["approval by the submitter -> unapproved"] = x["id"] in reconcile(effects, audits, ap)["flagged_ids"]
    return out


if __name__ == "__main__":
    r = reconcile(load(sys.argv[1]), load(sys.argv[2]), load(sys.argv[3]))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r["ok"] else 1)
