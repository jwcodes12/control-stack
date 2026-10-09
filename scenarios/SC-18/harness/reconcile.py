#!/usr/bin/env python3
"""SC-18 log-proxy test: independent reconciliation (prereg/SC18-LOG-PROXY.md).

Reads only (a) what the CLIENT actually received (status, request id, sha256 of the body it read, its own receive
time) and (b) the log SINK's files (the fsync'd record log and the commit-time file). It never reads the proxy's
journal or headers to decide. A released response is one the client received with status 200.

For every released response it requires, mirroring `SC18.RelOk` and `SC18.Good`:
  logged     : the sink log holds a record with the same request id          (r.id in the trusted log)
  digest     : that record's response digest equals sha256 of the body the client received
  before     : the record's commit time (sink stamp, after fsync) precedes the client's receive time
               (the record was in the log AT THE MOMENT OF RELEASE: r.llen <= logged.length, r.id in take r.llen)
  fresh      : receive time - commit time <= T   (r.clock <= r.lastAck + T; here the per-release ack is lastAck)
  nodup      : no request id is released twice                               ((released.map id).Nodup)
One host, one CLOCK_MONOTONIC: sink and client stamps are comparable.

Standalone:  python3 reconcile.py <client.jsonl> <sink.log> <commits.jsonl> <T seconds>
"""
import copy
import json
import sys


def load_jsonl(path):
    out = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def reconcile(client, sink, commits, T):
    commit_t = {(c["inc"], c["seq"]): c["t_commit"] for c in commits}
    by_rid = {}
    for r in sink:
        by_rid.setdefault(r["rid"], []).append(r)
    released = [c for c in client if c["status"] == 200]
    seen, dup_released = set(), []
    unlogged, mismatched, not_before, stale = [], [], [], []
    T_ns = int(T * 1e9)
    for c in released:
        rid = c["rid"]
        if rid in seen:
            dup_released.append(rid)
        seen.add(rid)
        recs = by_rid.get(rid)
        if not recs:
            unlogged.append({"rid": rid, "t_rx": c["t_rx"]})
            continue
        match = [r for r in recs if r["digest"] == c["digest"]]
        if not match:
            mismatched.append({"rid": rid, "client_digest": c["digest"], "log_digests": [r["digest"] for r in recs]})
            continue
        tc = [commit_t.get((r["inc"], r["seq"])) for r in match]
        tc = [t for t in tc if t is not None]
        if not tc or min(tc) >= c["t_rx"]:
            not_before.append({"rid": rid, "t_commit": min(tc) if tc else None, "t_rx": c["t_rx"]})
            continue
        if c["t_rx"] - max(t for t in tc if t < c["t_rx"]) > T_ns:
            stale.append({"rid": rid, "age_s": (c["t_rx"] - max(tc)) / 1e9})
    dup_logged = sorted(rid for rid, rs in by_rid.items() if len(rs) > 1)
    res = {"released": len(released), "logged_records": len(sink), "unlogged": unlogged, "mismatched": mismatched,
           "commit_not_before_release": not_before, "stale": stale, "dup_released": dup_released,
           "dup_logged_info": dup_logged}
    res["ok"] = not (unlogged or mismatched or not_before or stale or dup_released)
    return res


def mutation_selftest(client, sink, commits, T):
    """each entry True iff reconciliation flags the corresponding single defect injected into a copy"""
    out = {}
    rel = [c for c in client if c["status"] == 200]
    if not rel:
        return {"no released response to mutate": False}
    victim = rel[len(rel) // 2]["rid"]
    s1 = [r for r in sink if r["rid"] != victim]
    out["drop one record -> unlogged"] = len(reconcile(client, s1, commits, T)["unlogged"]) == 1
    s2 = copy.deepcopy(sink)
    for r in s2:
        if r["rid"] == victim:
            r["digest"] = "0" * 64
    out["alter one digest -> mismatched"] = len(reconcile(client, s2, commits, T)["mismatched"]) == 1
    c3 = copy.deepcopy(commits)
    rec = [r for r in sink if r["rid"] == victim][0]
    rx = [c for c in client if c["rid"] == victim][0]["t_rx"]
    for c in c3:
        if (c["inc"], c["seq"]) == (rec["inc"], rec["seq"]):
            c["t_commit"] = rx + 1
    out["commit after release -> not-before"] = len(reconcile(client, sink, c3, T)["commit_not_before_release"]) == 1
    c4 = copy.deepcopy(commits)
    for c in c4:
        if (c["inc"], c["seq"]) == (rec["inc"], rec["seq"]):
            c["t_commit"] = rx - int(T * 1e9) - 1
    out["ack older than T at release -> stale"] = len(reconcile(client, sink, c4, T)["stale"]) == 1
    cl = copy.deepcopy(client) + [dict(c, t_rx=c["t_rx"] + 1) for c in client if c["rid"] == victim]
    out["release one id twice -> dup"] = reconcile(cl, sink, commits, T)["dup_released"] == [victim]
    return out


if __name__ == "__main__":
    r = reconcile(load_jsonl(sys.argv[1]), load_jsonl(sys.argv[2]), load_jsonl(sys.argv[3]), float(sys.argv[4]))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r["ok"] else 1)
