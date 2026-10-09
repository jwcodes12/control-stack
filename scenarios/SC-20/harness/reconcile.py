#!/usr/bin/env python3
"""SC-20 data provenance: independent reconciliation (prereg/SC20-DATA-PROVENANCE.md).

Reads the TRAINER's log (what each run actually consumed, by digest), the SOURCES' own logs and the REVIEWER's own
log, plus the trusted allowlist. For every example consumed by a successful training run it requires (mirrors
SC20.Adm / sc20_safe, and the frozen-manifest re-check):
  frozen    : the consumed content's digest equals the digest frozen for that example in the run's manifest
  admitted  : an ALLOWLISTED source's log registers exactly that (id, digest), or the reviewer's log promotes exactly
              that (id, digest) and the reviewer is not the example's writer
NOTHING here says whether allowlisted or reviewed data is clean: that is semantic and outside this test.
"""
import copy
import json
import os


def load_committed(path):
    recs, commits = [], {}
    if os.path.exists(path):
        for l in open(path):
            if not l.strip():
                continue
            r = json.loads(l)
            if "commit" in r and len(r) == 2:
                commits[r["commit"]] = r["t"]
            else:
                recs.append(r)
    for r in recs:
        r["t"] = commits.get(r.get("seq"))
    return recs


def reconcile(runs, source_logs, reviews, allow):
    registered = {(r["id"], r["digest"]) for name, recs in source_logs.items() if name in allow for r in recs
                  if r["t"] is not None}
    promoted = {(r["id"], r["digest"]) for r in reviews if r["verdict"] == "promote" and r["reviewer"] != r["writer"]
                and r["t"] is not None}
    defects, consumed = [], 0
    for run in runs:
        if not run.get("ok"):
            continue
        frozen = {i: d for i, d in run["frozen"]}
        for i, d in run["consumed"]:
            consumed += 1
            why = []
            if frozen.get(i) != d:
                why.append("consumed content differs from the frozen digest")
            if (i, d) not in registered and (i, d) not in promoted:
                why.append("not registered by an allowlisted source nor promoted by a non-writer reviewer")
            if why:
                defects.append({"run": run["seq"], "id": i, "why": why})
    return {"runs": sum(1 for r in runs if r.get("ok")), "consumed": consumed, "defects": defects,
            "flagged": sorted({d["id"] for d in defects}), "ok": not defects}


def mutation_selftest(runs, source_logs, reviews, allow):
    ok_runs = [r for r in runs if r.get("ok") and r["consumed"]]
    if not ok_runs:
        return {"no consumed example to mutate": False}
    run = ok_runs[0]
    i, d = run["consumed"][0]
    fl = lambda rs, sl, rv, al: i in reconcile(rs, sl, rv, al)["flagged"]
    sl = {n: [r for r in recs if r["id"] != i] for n, recs in source_logs.items()}
    out = {"drop the registration / promotion of a consumed example -> flagged":
           fl(runs, sl, [r for r in reviews if r["id"] != i], allow)}
    rs = copy.deepcopy(runs)
    for r in rs:
        if r.get("seq") == run["seq"]:
            r["consumed"][0][1] = "0" * 64
    out["consumed content differs from the frozen digest -> flagged"] = fl(rs, source_logs, reviews, allow)
    reg = {(r["id"], r["digest"]) for name, recs in source_logs.items() if name in allow for r in recs}
    src_ex = [(x, y) for x, y in run["consumed"] if (x, y) in reg]
    if src_ex:
        j = src_ex[0][0]
        out["its source removed from the allowlist -> flagged"] = j in reconcile(runs, source_logs, reviews,
                                                                                   set())["flagged"]
    return out
