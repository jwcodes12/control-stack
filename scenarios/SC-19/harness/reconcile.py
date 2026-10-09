#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: independent reconciliation (prereg/SC19-TWO-PHASE.md).

Reads the production DB's own history table, the VERIFIER's and APPROVER's own logs, the snapshot service's log and
the gate's records. For every committed destructive operation d (mirroring `SC19.DestroyOk` / `sc19_safe`):
  in history : the DB history has a "destroy:<id>" row; the destroyed version is its ver_after - 1, the number of
               rows it removed is rows_changed, and their hash is rows_hash
  restore pt : the verifier's log has a VERIFIED record of d's snapshot, committed before d, whose recorded version
               of the target equals the destroyed version AND whose row hash equals the destroyed rows' hash (the
               restore point holds exactly what was destroyed)
  bounded    : rows removed (from the DB history) <= R
  approved   : the approver's log has a record of exactly d's operation digest (recomputed from the op it saw), for
               the same author, committed before d, by a principal other than the author
  once       : no operation id destroyed twice
restore_drill() restores a snapshot's rows for a target and compares them byte-exactly with the gate's dump of the
rows it deleted. Standalone:  python3 reconcile.py <stack dir> <R>
"""
import base64
import copy
import hashlib
import json
import os
import sqlite3
import sys


def load_jsonl(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def load_committed(path):
    recs, commits = [], {}
    for r in load_jsonl(path):
        if "commit" in r and len(r) == 2:
            commits[r["commit"]] = r["t"]
        else:
            recs.append(r)
    for r in recs:
        r["t"] = commits.get(r.get("seq"))
    return recs


def history(db):
    c = sqlite3.connect(db)
    try:
        return [dict(zip(("seq", "target", "ver_after", "kind", "rows_changed", "rows_hash", "t_ns"), r))
                for r in c.execute("SELECT seq, target, ver_after, kind, rows_changed, rows_hash, t_ns FROM history "
                                   "ORDER BY seq")]
    finally:
        c.close()


def op_digest(op):
    return hashlib.sha256(json.dumps({k: op[k] for k in ("id", "target", "kind", "author")}, sort_keys=True)
                          .encode()).hexdigest()


def reconcile(gates, verifs, approvals, hist, R):
    defects, seen = [], set()
    for g in gates:
        why = []
        h = [x for x in hist if x["kind"] == "destroy:" + g["id"]]
        if len(h) != 1:
            defects.append({"id": g["id"], "why": ["not exactly one destroy row in the DB history"]})
            continue
        h = h[0]
        ver, n, rh = h["ver_after"] - 1, h["rows_changed"], h["rows_hash"]
        if g["id"] in seen:
            why.append("destroyed twice")
        seen.add(g["id"])
        ok_v = any(v.get("verified") and v["snap_id"] == g["snap_id"] and v["t"] is not None and g["t"] is not None and
                   v["t"] < g["t"] and v["targets"].get(g["target"], {}).get("ver") == ver and
                   v["targets"].get(g["target"], {}).get("hash") == rh for v in verifs)
        if not ok_v:
            why.append("no verified restore point of exactly the destroyed version and rows")
        if n > R:
            why.append("affected %d > R = %d" % (n, R))
        ok_a = any(a["id"] == g["id"] and a["digest"] == g["digest"] and op_digest(a["op"]) == a["digest"] and
                   a["author"] == g["author"] and "approver:%d" % a["approver_pid"] != g["author"] and
                   a["t"] is not None and g["t"] is not None and a["t"] < g["t"] for a in approvals)
        if not ok_a:
            why.append("no approval of exactly this operation by another principal")
        if why:
            defects.append({"id": g["id"], "why": why})
    return {"destroys": len(gates), "defects": defects, "flagged": sorted({d["id"] for d in defects}),
            "ok": not defects}


def restore_drill(snap_file, target, deleted_rows):
    c = sqlite3.connect(snap_file)
    try:
        rows = sorted((int(i), bytes(p)) for i, p in c.execute("SELECT id, payload FROM objs WHERE target=?", (target,)))
    finally:
        c.close()
    dele = sorted((int(r["id"]), base64.b64decode(r["payload_b64"])) for r in deleted_rows)
    return {"restored": len(rows), "deleted": len(dele), "byte_exact": rows == dele}


def mutation_selftest(gates, verifs, approvals, hist, R):
    out = {}
    if not gates:
        return {"no destroy to mutate": False}
    g = gates[0]
    fl = lambda gs, vs, ap, hs: g["id"] in reconcile(gs, vs, ap, hs, R)["flagged"]
    out["drop the verification -> flagged"] = fl(gates, [v for v in verifs if v["snap_id"] != g["snap_id"]], approvals,
                                                hist)
    hs = copy.deepcopy(hist)
    for x in hs:
        if x["kind"] == "destroy:" + g["id"]:
            x["ver_after"] += 1
    out["destroyed version newer than the snapshot -> flagged"] = fl(gates, verifs, approvals, hs)
    hs = copy.deepcopy(hist)
    for x in hs:
        if x["kind"] == "destroy:" + g["id"]:
            x["rows_changed"] = R + 1
    out["affected > R in the DB history -> flagged"] = fl(gates, verifs, approvals, hs)
    out["drop the approval -> flagged"] = fl(gates, verifs, [a for a in approvals if a["id"] != g["id"]], hist)
    ap = copy.deepcopy(approvals)
    for a in ap:
        if a["id"] == g["id"]:
            a["op"]["target"] = "another-target"
    out["approval of a different operation -> flagged"] = fl(gates, verifs, ap, hist)
    return out


if __name__ == "__main__":
    st, R = sys.argv[1], int(sys.argv[2])
    print(json.dumps(reconcile(load_committed(os.path.join(st, "gate.jsonl")),
                               load_committed(os.path.join(st, "verifier.jsonl")),
                               load_committed(os.path.join(st, "approver.jsonl")),
                               history(os.path.join(st, "prod.db")), R), indent=1))
