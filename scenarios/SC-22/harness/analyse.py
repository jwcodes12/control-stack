#!/usr/bin/env python3
"""SC-22 replication sampling: analysis of one repetition (prereg/SC22-REPLICATION.md).

From the REPORTER's log (which findings it misreported, per trial) and the REPLICATOR's log (sample, flags, detected,
commitment and draw times), per configuration:
  structural : the replicator's verdict equals (sample meets the misreported set) in every trial, its flags are
               exactly sample ∩ misreported, and every hidden sample was drawn after the reports were committed
  survival   : the fraction of trials with no flag, against the exact value C(N-k,B)/C(N,B)
               (EvalIntegrity.sc22_unreplicated_misreport) via an exact two-sided Clopper-Pearson interval
  uniformity : each finding's inclusion count across the hidden samples, against Binomial(n, B/N)
"""
import copy
import math
from statistics import NormalDist

import stats as ST


def per_config(rep_log, rpl_log, cfg):
    mis = {r["t"]: set(r["misreported"]) for r in rep_log if r["config"] == cfg}
    rows = [r for r in rpl_log if r.get("ev") == "replicate" and r["config"] == cfg]
    commit = [r for r in rpl_log if r.get("ev") == "commit" and r["config"] == cfg]
    return mis, rows, commit


def structural(rep_log, rpl_log, cfg):
    mis, rows, commit = per_config(rep_log, rpl_log, cfg)
    bad = []
    t_commit = commit[-1]["t"] if commit else None
    for r in rows:
        A = mis.get(r["t"], set())
        if r["detected"] != bool(set(r["sample"]) & A) or sorted(set(r["sample"]) & A) != r["flags"]:
            bad.append({"t": r["t"], "why": "verdict differs from sample ∩ misreported"})
        if not r["visible"] and (t_commit is None or r["t_draw"] <= t_commit):
            bad.append({"t": r["t"], "why": "hidden sample drawn before the commitment"})
    return {"trials": len(rows), "defects": bad[:5], "n_defects": len(bad), "ok": not bad and len(rows) == len(mis) > 0}


def survival_test(rep_log, rpl_log, cfg, N, B, k, level):
    _, rows, _ = per_config(rep_log, rpl_log, cfg)
    n = len(rows)
    x = sum(1 for r in rows if not r["detected"])
    exact = float(ST.bound_hidden(N, B, k))
    lo, hi = ST.clopper_pearson(x, n, level)
    return {"trials": n, "undetected": x, "survival": x / n if n else None, "exact": exact, "ci": [lo, hi],
            "contains_exact": lo <= exact <= hi}


def uniformity(rpl_log, cfgs, N, B, alpha):
    rows = [r for r in rpl_log if r.get("ev") == "replicate" and r["config"] in cfgs and not r["visible"]]
    n = len(rows)
    cnt = [0] * N
    for r in rows:
        for i in r["sample"]:
            cnt[i] += 1
    p = B / N
    z = [(c - n * p) / math.sqrt(n * p * (1 - p)) for c in cnt]
    zc = NormalDist().inv_cdf(1 - alpha / (2 * N))
    return {"samples": n, "max_abs_z": max(abs(v) for v in z), "z_crit": zc, "ok": max(abs(v) for v in z) <= zc}


def mutation_selftest(rep_log, rpl_log, cfg):
    out = {}
    rows = [r for r in rpl_log if r.get("ev") == "replicate" and r["config"] == cfg]
    if not rows:
        return {"no trial to mutate": False}
    l = copy.deepcopy(rpl_log)
    for r in l:
        if r.get("ev") == "replicate" and r["config"] == cfg:
            r["detected"] = not r["detected"]
            break
    out["one replicator verdict flipped -> structural check fails"] = not structural(rep_log, l, cfg)["ok"]
    l = copy.deepcopy(rpl_log)
    for r in l:
        if r.get("ev") == "commit" and r["config"] == cfg:
            r["t"] = rows[0]["t_draw"] + 1
    out["hidden sample drawn before the commitment -> structural check fails"] = not structural(rep_log, l, cfg)["ok"]
    return out
