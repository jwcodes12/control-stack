#!/usr/bin/env python3
"""SC-17 drift reconcile: independent reconciliation (prereg/SC17-DRIFT-RECONCILE.md).

Drift (from the CLUSTER's own mutation log, which holds the full live set after every mutation, so the live state is
known at every instant, not just at samples; mirrors SC17Drift):
  count(t)    = out-of-band grants live at t (the injector names them "oob-*"; the model's ghost `drift` list), and
                |live \ base| (live minus the last state pushed by the gate or reconciler; the model's live \ desired)
  lifetime(g) = time g left the live set - time it entered; grants still live at the end are reported as censored
Applies (from the gate's apply log and the REVIEWER's own log; mirrors SC17.AppOk / sc17_safe):
  every apply has a reviewer record for the same id with EXACTLY the applied diff and the same author, committed
  before the apply, by a reviewer other than the author; the resulting desired state satisfies the ceiling; the push
  to the cluster succeeded and the cluster's live state right after it equals that desired state
Ceiling over time: no live state in the cluster log ever holds a forbidden combination produced by applies.
Standalone:  python3 reconcile.py <stack dir> <W ticks> <tick s> <d>
"""
import copy
import json
import os
import sys


def forbidden(grants):
    gs = {tuple(g) for g in grants}
    return sorted({s for (s, v, r) in gs if (s, "read", "secrets") in gs and (s, "exec", "prod") in gs})


def load_jsonl(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def load_committed(path):
    recs, commits = [], {}
    for r in load_jsonl(path):
        if "commit" in r:
            commits[r["commit"]] = r["t"]
        else:
            recs.append(r)
    for r in recs:
        r["t"] = commits.get(r["seq"])
    return recs


def is_oob(g):
    return str(g[0]).startswith("oob-")


def drift(events, t_end=None, checkpoints=(), t0=None):
    events = sorted(events, key=lambda e: e["seq"])
    birth, life, prev = {}, [], set()
    max_oob = max_base = 0
    series = []
    for e in events:
        live = {tuple(g) for g in e["live"]}
        base = {tuple(g) for g in e["base"]}
        for g in live - prev:
            if is_oob(g):
                birth[g] = e["t"]
        for g in prev - live:
            if is_oob(g) and g in birth:
                life.append({"grant": list(g), "born": birth[g], "lifetime_s": (e["t"] - birth.pop(g)) / 1e9})
        prev = live
        n_oob = sum(1 for g in live if is_oob(g))
        max_oob = max(max_oob, n_oob)
        max_base = max(max_base, len(live - base))
        series.append((e["t"], n_oob))
    t_end = t_end if t_end is not None else (events[-1]["t"] if events else 0)
    alive = [{"grant": list(g), "born": b, "age_s": (t_end - b) / 1e9} for g, b in birth.items()]
    cps = []
    if t0 is not None:
        for c in checkpoints:
            tc = t0 + int(c * 1e9)
            n = 0
            for t, k in series:
                if t <= tc:
                    n = k
            cps.append({"c_s": c, "oob_live": n})
    return {"max_oob_live": max_oob, "max_live_minus_base": max_base, "n_died": len(life),
            "max_lifetime_s": max((x["lifetime_s"] for x in life), default=0.0), "alive_at_end": alive,
            "max_age_alive_s": max((x["age_s"] for x in alive), default=0.0), "checkpoints": cps,
            "n_born": len(life) + len(alive)}


def audit_applies(applies, reviews, events):
    bad = []
    by_v = {e["version"]: e for e in events if e["kind"] == "set_state" and e.get("by") == "gate"}
    for a in applies:
        why = []
        if a["t"] is None:
            why.append("apply record not committed")
        ok_r = any(r["id"] == a["id"] and r["diff"] == a["diff"] and r["author"] == a["author"] and
                   r["t"] is not None and a["t"] is not None and r["t"] < a["t"] for r in reviews)
        if not ok_r:
            why.append("no reviewer record of exactly this diff before the apply")
        if a.get("approval", {}).get("reviewer") == a["author"]:
            why.append("reviewer is the author")
        if forbidden(a["desired"]):
            why.append("resulting desired state violates the ceiling: %s" % forbidden(a["desired"]))
        e = by_v.get(a["version"])
        if not (a.get("push", {}).get("ok") and e is not None and
                sorted(map(tuple, e["live"])) == sorted(map(tuple, a["desired"]))):
            why.append("cluster live state after the push differs from the desired state")
        if why:
            bad.append({"id": a["id"], "why": why})
    ceiling_live = sorted({e["seq"] for e in events if forbidden([g for g in e["live"] if not is_oob(g)])})
    return {"applies": len(applies), "defects": bad, "live_states_over_ceiling": ceiling_live,
            "ok": not bad and not ceiling_live}


def mutation_selftest(applies, reviews, events, bound_life):
    out = {}
    if applies:
        ap = copy.deepcopy(applies)
        ap[0]["diff"] = {"adds": [["mallory", "exec", "prod"]], "dels": []}
        out["applied diff differs from the reviewed diff -> flagged"] = not audit_applies(ap, reviews, events)["ok"]
        ap = copy.deepcopy(applies)
        ap[-1]["desired"] = ap[-1]["desired"] + [["zed", "read", "secrets"], ["zed", "exec", "prod"]]
        out["forbidden resulting state -> flagged"] = not audit_applies(ap, reviews, events)["ok"]
    reverts = [e for e in events if e["kind"] == "set_state" and e.get("removed")]
    if reverts:
        ev = [e for e in events if e is not reverts[0]]
        # without that revert the grants it removed stay live until the next mutation that drops them
        ev2 = copy.deepcopy(ev)
        rm = {tuple(g) for g in reverts[0]["removed"]}
        for e in ev2:
            if e["seq"] > reverts[0]["seq"]:
                e["live"] = sorted({tuple(g) for g in e["live"]} | rm)
        d = drift(ev2)
        out["drop one reconciler revert -> a lifetime exceeds the bound"] = (
            max(d["max_lifetime_s"], d["max_age_alive_s"]) > bound_life)
    return out


if __name__ == "__main__":
    st = sys.argv[1]
    ev = load_jsonl(os.path.join(st, "cluster.jsonl"))
    print(json.dumps({"drift": drift(ev), "applies": audit_applies(load_committed(os.path.join(st, "gate.jsonl")),
                                                                    load_committed(os.path.join(st, "reviewer.jsonl")),
                                                                    ev)}, indent=1))
