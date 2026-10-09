#!/usr/bin/env python3
"""DC-1 single-host rehearsal: analysis of one repetition's stored sink log (prereg/DC1-REHEARSAL-SINGLEHOST.md).

Pure functions over the sink's JSONL log (and, for the delivery premise only, the workers' HALTED reports). All
landing times are the sink's own CLOCK_MONOTONIC stamps. t0 is the sink's stamp of the controller's MARK; tF is the
sink's stamp of the BUMP (the moment the fence takes effect), so eps_hat = tF - t0 is the measured epsilon.

Counting follows `ControlStack/Families/F3/DistributedHalt.lean`:
  accepted_after(t)  = #{accepted effects with landing time >= t}     (countP (fun ev => t <= ev.1) of sinkRun)

The decision rules (`rule_*`) are what the runner checks; `mutation_selftest` shows each rule can fire on a stored
log. Also usable standalone:  python3 analyse.py <sink.log>   (prints the measured quantities).
"""
import copy
import json
import math
import sys


def load_log(path):
    effects, ctl, bad = [], {}, []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if "ctl" in r:
                ctl.setdefault(r["ctl"], []).append(r)
            elif "bad" in r:
                bad.append(r)
            else:
                effects.append(r)
    return effects, ctl, bad


def epoch_at(ctl, e0, t):
    """the sink's current epoch at sink time t, reconstructed from the BUMP control records"""
    cur = e0
    for b in sorted(ctl.get("BUMP", []), key=lambda r: r["t"]):
        if b["t"] <= t:
            cur = b["epoch"]
    return cur


def measure(effects, ctl, bad, workers, p, partitioned=(), checkpoints=()):
    """workers: {id: {"HALTED": {...} or None}}; p: dict with n, rho, e0, fence (bool)"""
    t0 = ctl["MARK"][0]["t"]
    tF = ctl["BUMP"][0]["t"] if ctl.get("BUMP") else None
    m = {"t0_ns": t0, "tF_ns": tF, "eps_hat_s": None if tF is None else (tF - t0) / 1e9,
         "n_effects": len(effects), "n_bad": len(bad)}
    # in-flight latency (landing minus initiation; one host, one CLOCK_MONOTONIC)
    lat = [(e["t"] - e["ti"]) / 1e9 for e in effects]
    m["L_hat_s"] = max(lat) if lat else 0.0
    m["lat_p50_s"] = sorted(lat)[len(lat) // 2] if lat else None
    # delivery delays (worker-reported HALT receipt, same host clock)
    deltas, absorb_viol = {}, []
    for w, rep in sorted(workers.items()):
        h = rep.get("HALTED")
        if h is None:
            continue
        deltas[w] = (h["t_rx"] - t0) / 1e9
        late = [e for e in effects if e["w"] == w and e["ti"] > h["t_rx"]]
        if late:
            absorb_viol.append({"w": w, "n": len(late), "first_ti": late[0]["ti"], "t_rx": h["t_rx"]})
    m["delta_hat_s"] = {str(w): round(d, 6) for w, d in deltas.items()}
    m["Delta_hat_s"] = max(deltas.values()) if deltas else None
    m["undelivered"] = sorted(w for w in workers if workers[w].get("HALTED") is None)
    m["absorb_violations"] = absorb_viol
    # rate premise: spacing between consecutive initiations of each worker
    gaps = {}
    by_w = {}
    for e in effects:
        by_w.setdefault(e["w"], []).append(e)
    seq_gaps = {}
    for w, es in by_w.items():
        es = sorted(es, key=lambda e: e["s"])
        g = [(b["ti"] - a["ti"]) / 1e9 for a, b in zip(es, es[1:])]
        gaps[w] = min(g) if g else None
        sq = [e["s"] for e in es]
        if sq != list(range(sq[0], sq[0] + len(sq))) or sq[0] != 0:
            seq_gaps[w] = {"first": sq[0], "n": len(sq), "last": sq[-1]}
    m["min_gap_s"] = {str(w): g for w, g in sorted(gaps.items())}
    m["seq_gaps"] = {str(w): v for w, v in seq_gaps.items()}
    # sink decision vs the registered rule
    mism = []
    for e in effects:
        want = (not p["fence"]) or e["e"] >= epoch_at(ctl, p["e0"], e["t"])
        if bool(e["acc"]) != want:
            mism.append(e)
    m["rule_mismatches"] = len(mism)
    m["rule_mismatch_examples"] = mism[:5]
    acc = [e for e in effects if e["acc"]]
    m["A_t0"] = sum(1 for e in acc if e["t"] >= t0)
    m["A_tF"] = None if tF is None else sum(1 for e in acc if e["t"] >= tF)
    m["A_t0_by_worker"] = {str(w): sum(1 for e in acc if e["t"] >= t0 and e["w"] == w) for w in sorted(by_w)}
    if tF is not None:
        m["A_tF_by_worker"] = {str(w): sum(1 for e in acc if e["t"] >= tF and e["w"] == w) for w in sorted(by_w)}
        m["R_tF_by_worker"] = {str(w): sum(1 for e in effects if not e["acc"] and e["t"] >= tF and e["w"] == w)
                               for w in sorted(by_w)}
        m["epochs_accepted_after_tF"] = sorted({e["e"] for e in acc if e["t"] >= tF})
    last_acc = max((e["t"] for e in acc), default=None)
    m["quiescence_after_t0_s"] = None if last_acc is None or last_acc < t0 else (last_acc - t0) / 1e9
    # bounds from DistributedHalt with measured L_hat, Delta_hat, eps_hat
    n, rho = p["n"], p["rho"]
    if m["Delta_hat_s"] is not None:
        m["B_unfenced"] = n * rho * (m["L_hat_s"] + m["Delta_hat_s"])          # landed_after_le
        m["B_unfenced_sum"] = sum(rho * (m["L_hat_s"] + d) for d in deltas.values())  # per-node form
    if m["eps_hat_s"] is not None:
        m["B_fenced"] = n * rho * (m["L_hat_s"] + m["eps_hat_s"])              # fenced_window
    # partitioned workers' accepted landings after t0 at checkpoints t0 + c
    m["partition_series"] = {}
    for w in partitioned:
        m["partition_series"][str(w)] = [
            {"c_s": c, "accepted": sum(1 for e in acc if e["w"] == w and t0 <= e["t"] < t0 + int(c * 1e9))}
            for c in checkpoints]
    return m


# ---------------------------------------------------------------- decision rules (prereg §3)
def rule_h1(m, tau):
    """unfenced, bounded delivery: A_t0 <= n*rho*(L_hat + Delta_hat) + tau"""
    return m.get("B_unfenced") is not None and m["A_t0"] <= m["B_unfenced"] + tau


def rule_h2(m):
    """fenced: zero accepted landings at or after tF (= t0 + eps_hat)"""
    return m["A_tF"] == 0


def rule_h2_window(m, tau):
    """fenced window: A_t0 <= n*rho*(L_hat + eps_hat) + tau (no delivery premise)"""
    return m["A_t0"] <= m["B_fenced"] + tau


def rule_h3(m, w, rho, frac, B_plus_tau):
    """partition control fires: the partitioned worker's accepted landings after t0 strictly increase over the
    checkpoints, grow at >= frac*rho per second, and the total exceeds the bounded-delivery bound"""
    s = [x["accepted"] for x in m["partition_series"][str(w)]]
    cs = [x["c_s"] for x in m["partition_series"][str(w)]]
    increasing = all(b > a for a, b in zip(s, s[1:]))
    slope = (s[-1] - s[0]) / (cs[-1] - cs[0]) if len(s) > 1 else 0.0
    return {"series": s, "increasing": increasing, "slope_per_s": slope, "slope_ok": slope >= frac * rho,
            "exceeds_bound": m["A_t0"] > B_plus_tau,
            "fires": increasing and slope >= frac * rho and m["A_t0"] > B_plus_tau}


def rule_h4(m, leaked):
    """token-leak control fires: >= 1 accepted landing at or after tF from the worker holding the new epoch, and
    zero from every other worker"""
    leak = m["A_tF_by_worker"].get(str(leaked), 0)
    others = {w: v for w, v in m["A_tF_by_worker"].items() if w != str(leaked) and v}
    return {"leaked_accepted_after_tF": leak, "others_accepted_after_tF": others,
            "fires": leak >= 1 and not others}


# ---------------------------------------------------------------- analysis sensitivity (mutation self-test)
def mutation_selftest(effects, ctl, bad, workers, p, tau, which, **kw):
    """Re-run a rule on a mutated copy of the stored log; each entry is True iff the rule's verdict flips as it
    must (so the rule can fire on real logs)."""
    out = {}
    t0 = ctl["MARK"][0]["t"]
    if which == "h1":
        ev = copy.deepcopy(effects)
        m0 = measure(ev, ctl, bad, workers, p)
        k = int(math.floor(m0["B_unfenced"] + tau)) + 1 - m0["A_t0"]
        for i in range(max(k, 1)):
            ev.append({"t": t0 + 1000 + i, "w": 0, "s": 10 ** 6 + i, "e": p["e0"], "ti": t0 + 1000 + i,
                       "acc": True, "cur": p["e0"]})
        out["h1: inject accepted landings past the bound -> rule fails"] = not rule_h1(
            measure(ev, ctl, bad, workers, p), tau)
    elif which == "h2":
        tF = ctl["BUMP"][0]["t"]
        ev = copy.deepcopy(effects)
        ev.append({"t": tF + 1, "w": 0, "s": 10 ** 6, "e": p["e0"], "ti": tF, "acc": True, "cur": p["e0"] + 1})
        m1 = measure(ev, ctl, bad, workers, p)
        out["h2: inject one accepted old-epoch landing after the fence -> rule fails"] = not rule_h2(m1)
        out["h2: the injected record is flagged as inconsistent with the sink rule"] = m1["rule_mismatches"] >= 1
    elif which == "h3":
        w = kw["w"]
        ev = [e for e in effects if not (e["w"] == w and e["acc"] and e["t"] >= t0)]
        m1 = measure(ev, ctl, bad, workers, p, partitioned=[w], checkpoints=kw["checkpoints"])
        out["h3: drop the partitioned worker's landings after t0 -> control does not fire"] = not rule_h3(
            m1, w, p["rho"], kw["frac"], kw["B_plus_tau"])["fires"]
    elif which == "h4":
        w, tF = kw["w"], ctl["BUMP"][0]["t"]
        ev = copy.deepcopy(effects)
        for e in ev:
            if e["w"] == w and e["t"] >= tF:
                e["acc"] = False
        out["h4: reject the leaked worker's after-fence landings -> control does not fire"] = not rule_h4(
            measure(ev, ctl, bad, workers, p), w)["fires"]
    return out


if __name__ == "__main__":
    ef, ct, bd = load_log(sys.argv[1])
    print(json.dumps(measure(ef, ct, bd, {}, {"n": 8, "rho": 50.0, "e0": 1, "fence": True}), indent=1,
                     default=str))
