#!/usr/bin/env python3
"""SC-10/11: independent reconciliation (prereg/SC10-POLICY-STORE.md).

Decisions (mirrors SC10.DecOk / sc10_safe): from the STORE's own log (versions with writer and commit stamp) and the
enforcement point's decision log, on the shared CLOCK_MONOTONIC clock. For every decision d:
  from store : d used a store version (not some other source)
  latest     : d's version is the newest version committed at or before the moment the policy was applied
               (d.t_answer)
  admin      : that version was written by the admin
  applied    : d's allow/deny equals that version's allow list applied to d's host
Stale decisions (an older version applied after a newer one committed) are counted and their staleness measured.
Builds (path_toolchain): every build output records the SHA-256 of the toolchain that actually ran; it must equal the
pinned digest.
"""
import copy
import json
import os


def load_jsonl(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def store_versions(path):
    recs, commits = [], {}
    for r in load_jsonl(path):
        if "commit" in r and len(r) == 2:
            commits[r["commit"]] = r["t"]
        else:
            recs.append(r)
    for r in recs:
        r["t_commit"] = commits.get(r["version"])
    return recs


def reconcile_decisions(versions, decisions):
    bad, stale = [], []
    by_v = {v["version"]: v for v in versions}
    for d in decisions:
        why = []
        if d.get("version") is None:
            why.append("decision not from the store")
        else:
            committed = [v for v in versions if v["t_commit"] is not None and v["t_commit"] <= d["t_answer"]]
            latest = max((v["version"] for v in committed), default=None)
            if d["version"] != latest:
                why.append("not the latest version at that moment (used %s, latest %s)" % (d["version"], latest))
                newer = [v for v in committed if v["version"] > d["version"]]
                if newer:
                    stale.append((d["t_answer"] - min(v["t_commit"] for v in newer)) / 1e9)
            v = by_v.get(d["version"])
            if v is None or v["writer"] != "admin":
                why.append("version not written by the admin")
            elif (d["host"] in v["policy"].get("allow", [])) != (d["decision"] == "allow"):
                why.append("decision does not apply the version's policy")
        if why:
            bad.append({"host": d["host"], "version": d.get("version"), "why": why})
    return {"decisions": len(decisions), "versions_used": sorted({d.get("version") for d in decisions},
                                                                   key=lambda x: -1 if x is None else x),
            "defects": bad[:10], "n_defects": len(bad), "stale_decisions": len(stale),
            "max_staleness_s": max(stale) if stale else 0.0, "ok": not bad}


def reconcile_builds(outputs, pinned_digest):
    bad = [o for o in outputs if o.get("self_sha256") != pinned_digest]
    return {"builds": len(outputs), "defects": bad, "ok": not bad}


def mutation_selftest(versions, decisions, outputs, pinned_digest):
    out = {}
    ds = [d for d in decisions if d.get("version") is not None]
    if ds:
        m = copy.deepcopy(decisions)
        for d in m:
            if d is not None and d.get("version") == ds[-1]["version"] and d["t_answer"] == ds[-1]["t_answer"]:
                d["version"] -= 1
        out["a decision using an older version -> flagged"] = not reconcile_decisions(versions, m)["ok"]
    if ds:
        v = copy.deepcopy(versions)
        for x in v:
            if x["version"] == ds[0]["version"]:
                x["writer"] = "pid:1"
        out["a version not written by the admin -> flagged"] = not reconcile_decisions(v, decisions)["ok"]
    if outputs:
        o = copy.deepcopy(outputs)
        o[0]["self_sha256"] = "0" * 64
        out["a build with another toolchain -> flagged"] = not reconcile_builds(o, pinned_digest)["ok"]
    return out
