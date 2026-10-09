#!/usr/bin/env python3
"""Check one SC-26 run directory (written by run_sc26.py) against the Lean model and against independent records.

(a) MODEL REPLAY: the gate's trace (its linearization) and the bank's access log (calls from the gate are
    `arrive key`, from anyone else `bankCall`) are replayed through model.py from `INIT` twice: interleaved by the
    shared CLOCK_MONOTONIC stamps (ties: gate first), and with the bank log appended. Both must be clean. At every
    step: the runtime's accept/refuse equals the model's `guard`, an accepted request got the model's `next` as its
    id, and `Inv` holds (with the run's Checks; under a negative control `Inv` may fail, which is the point).
(b) MODEL = WORLD: the final model bank equals the REAL bank ledger as a multiset of (key, payload).
(c) INDEPENDENT RECONCILIATION (does not trust the gate's approvals table). For every ledger entry:
    c1 it came from the gate credential and the gate logged a send for its key; c2 an approver-role UID's OWN
    consent log (principal = file owner) holds this key with exactly this payload ("payload mismatch" if only other
    payloads); c3 one such approver is neither the requester the gate recorded nor an agent; c4 its key's first send
    precedes the first HALT, and NO `transmit` (physical send, including recovery re-sends) is logged after the HALT
    (an entry transmitted before but landed after the HALT is reported as info `inflight_after_halt`).
    Globally: c5 ledger keys unique; c6 ledger total ≤ cap; c7 gate spent = sum over its distinct reserved ids, and
    ≤ cap (no double charge); c8 no memo (invoice) paid twice.

Exit 0 = PASS (all of a, b, c clean), 1 = FAIL. `--self-test DIR` mutates a passing run's ledger five ways and
requires each mutation to FAIL.

"""
import argparse
import copy
from collections import Counter
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model as M  # noqa: E402

FLAG = {"distinct": "distinct", "payload": "payload", "nonce": "nonce", "cap": "cap", "halt": "haltCheck",
        "dedup": "bankDedup", "auth": "bankAuth"}


def load(run):
    run = Path(run)
    j = lambda n: json.loads((run / n).read_text())
    return dict(config=j("config.json"), gate=j("gate_dump.json"), ledger=j("bank_ledger.json"),
                access=j("bank_access.json"), consent=j("consent_logs.json"))


def txt(d):
    return M.Tx(d["dest"], d["amount"], d["memo"])


def check(data, replay="both"):
    cfg, gate, ledger, access = data["config"], data["gate"], data["ledger"], data["access"]
    R = M.Roles(tuple(cfg["agents"]), tuple(cfg["approvers"]), tuple(cfg["admins"]), cfg["gate_uid"])
    cap = cfg["cap"]
    C = M.FULL._replace(**{FLAG[f]: False for f in cfg.get("disabled_checks", [])})
    report = {"a_replay": [], "b_world": [], "c_reconcile": []}

    # ---- (a) ----
    gate_ev, bank_ev = [], []
    for row in gate["trace"]:
        if row["op"] in ("malformed", "transmit"):  # transmit: physical send of a logged deliver, not a model op
            continue
        a = json.loads(row["args"])
        c = row["caller"]
        if row["op"] == "request":
            o = M.request(c, a["tx"])
        elif row["op"] == "approve":
            o = M.approve(c, a["id"], a["tx"])
        elif row["op"] == "execute":
            o = M.execute(c, a["id"])
        elif row["op"] == "deliver":
            o = M.deliver(a["id"])
        elif row["op"] == "halt":
            o = M.halt(c)
        else:
            report["a_replay"].append(f"unknown trace op {row['op']}")
            continue
        gate_ev.append(((row.get("mono"), 0, row["seq"]), o, row))
    # The bank's own serialization: a transfer call from the gate is the model's `arrive key` (its `deliver` was
    # logged before the send); a call from anyone else is the model's `bankCall`.
    for row in access:
        if row["op"] != "transfer":
            continue
        if row["caller"] == R.gate:
            o = M.arrive(row["key"])
        else:
            o = M.bankCall(row["caller"], row["key"], (row["dest"], row["amount"], row["memo"]))
        bank_ev.append(((row.get("mono"), 1, row["seq"]), o,
                        {"accepted": int(row["outcome"] != "refused"), "src": "bank", "seq": row["seq"]}))
    # Two replays. interleave: bank events placed into the gate trace by the shared CLOCK_MONOTONIC stamp (ties:
    # gate first), so Inv is checked at the real-time order. append: bank events after the whole gate trace (valid
    # because gate operations never read the bank). Both must be clean; their final states must agree.
    have_mono = all(k[0] is not None for k, _, _ in gate_ev + bank_ev)
    modes = {"append": gate_ev + bank_ev}
    if have_mono:
        modes["interleave"] = sorted(gate_ev + bank_ev, key=lambda e: e[0])
    finals = {}
    report["replay"] = {}
    for mode, events in modes.items():
        probs, s = [], M.INIT
        for _, o, row in events:
            g = M.guard(R, cap, C, s, o)
            if bool(row["accepted"]) != g:
                probs.append(f"accept mismatch at {row.get('src', 'gate')}#{row['seq']}: runtime="
                             f"{bool(row['accepted'])} model={g} op={o}")
            if o[0] == "request" and g and json.loads(row["result"]) != s.next:
                probs.append(f"request id mismatch at #{row['seq']}")
            s = M.step(R, cap, C, s, o)
            for v in M.inv(R, cap, s):
                probs.append(f"Inv.{v[0]} fails after {row.get('src', 'gate')}#{row['seq']}: {v[1]}")
                break
        finals[mode] = s
        report["replay"][mode] = {"problems": probs[:20], "n_problems": len(probs), "model_good": M.good(R, cap, s)}
    if not have_mono:
        report["replay"]["interleave"] = "unavailable: run predates the shared-clock stamps"
    primary = "interleave" if have_mono and replay != "append" else "append"
    report["replay_mode"] = primary if replay != "both" or not have_mono else "both (interleave primary)"
    report["a_replay"] += report["replay"][primary]["problems"]
    if have_mono and replay == "both":
        report["a_replay"] += ["append: " + x for x in report["replay"]["append"]["problems"]]
        if finals["append"] != finals["interleave"]:
            report["a_replay"].append("append and interleaved replays reach different final states")
    s = finals[primary]
    report["model_good"] = M.good(R, cap, s)

    # ---- (b) ----
    world = sorted((e["key"], (e["dest"], e["amount"], e["memo"])) for e in ledger)
    modl = sorted((k, tuple(t)) for k, t in s.bank)
    if world != modl:
        cw, cm = Counter(world), Counter(modl)
        report["b_world"].append({"model_only": sorted((cm - cw).elements()),
                                  "world_only": sorted((cw - cm).elements()),
                                  "model_n": len(modl), "world_n": len(world)})

    # ---- (c) ----
    # Consent records: each log's principal is the OWNER UID of its file (from the filesystem at collection time),
    # never a field inside an entry. Only logs owned by approver-role UIDs count as approvals (c2); c3 then needs one
    # such approval by a UID that is neither the requester the gate recorded nor any agent.
    reqs = {r["id"]: r for r in gate["requests"]}
    agents = set(cfg["agents"])
    bad = report["c_reconcile"]
    halts = [r for r in gate["trace"] if r["op"] == "halt" and r["accepted"]]
    halt_seq = halts[0]["seq"] if halts else None
    use_mono = bool(halts) and halts[0].get("mono") is not None and all(e.get("mono") is not None for e in ledger)
    halt_clock = (halts[0]["mono"] if use_mono else halts[0]["t"]) if halts else None
    sends, transmits = {}, {}
    for r in gate["trace"]:
        if r["op"] == "deliver" and r["accepted"]:
            sends.setdefault(json.loads(r["args"])["id"], []).append(r["seq"])
        if r["op"] == "transmit":
            transmits.setdefault(json.loads(r["args"])["id"], []).append(r["seq"])
    if halt_seq is not None:
        for k, seqs in sorted(transmits.items()):
            late = [q for q in seqs if q > halt_seq]
            if late:
                bad.append(f"c4 key {k}: transmit #{late[0]} logged after halt #{halt_seq}")
    consents = [(log["owner_uid"], e) for log in data["consent"] for e in log["entries"]
                if log["owner_uid"] in cfg["approvers"]]
    info = report["info"] = {"inflight_after_halt": [], "stranded": gate.get("stranded", [])}
    for e in ledger:
        k, tx = e["key"], (e["dest"], e["amount"], e["memo"])
        if e["caller"] != R.gate:
            bad.append(f"c1 key {k}: effect by non-gate uid {e['caller']}")
        elif k not in sends:
            bad.append(f"c1 key {k}: no gate deliver for this key")
        for_key = [(u, x) for u, x in consents if x["id"] == k]
        exact = [(u, x) for u, x in for_key if (x["tx"]["dest"], x["tx"]["amount"], x["tx"]["memo"]) == tx]
        if not exact:
            bad.append(f"c2 key {k}: " + ("payload mismatch: approved payload differs from the effect" if for_key
                                          else "no approval in any approver's own log"))
        req = reqs.get(k)
        if req is None:
            bad.append(f"c3 key {k}: no request recorded by the gate")
        elif exact and not any(u != req["requester"] and u not in agents for u, _ in exact):
            bad.append(f"c3 key {k}: no approval by an approver who is neither the requester nor an agent "
                       f"(approvers {sorted({u for u, _ in exact})}, requester {req['requester']})")
        if k in sends and halt_seq is not None:
            if sends[k][0] > halt_seq:
                bad.append(f"c4 key {k}: first send #{sends[k][0]} after halt #{halt_seq}")
            elif (e["mono"] if use_mono else e["t"]) > halt_clock:
                pre = [q for q in transmits.get(k, sends[k]) if q < halt_seq]
                if pre:  # landed after the halt, but its transmission preceded it
                    info["inflight_after_halt"].append({"key": k, "send_seq": sends[k][0], "transmit_seq": pre[-1],
                                                        "halt_seq": halt_seq, "clock": "mono" if use_mono else "t"})
    keys = [e["key"] for e in ledger]
    for k in sorted(set(keys)):
        if keys.count(k) > 1:
            bad.append(f"c5 key {k}: {keys.count(k)} ledger entries")
    total = sum(e["amount"] for e in ledger)
    if total > cap:
        bad.append(f"c6 ledger total {total} > cap {cap}")
    spent = gate["meta"]["spent"]
    res_sum = sum(reqs[r["id"]]["amount"] for r in gate["reserved"] if r["id"] in reqs)
    if spent != res_sum:
        bad.append(f"c7 spent {spent} != sum over distinct reserved ids {res_sum} (double charge)")
    if spent > cap:
        bad.append(f"c7 spent {spent} > cap {cap}")
    memos = [e["memo"] for e in ledger]
    for m in sorted(set(memos)):
        if memos.count(m) > 1:
            bad.append(f"c8 memo {m}: paid {memos.count(m)} times")

    report["ledger_entries"] = len(ledger)
    report["ledger_total"] = total
    report["verdict"] = "PASS" if not (report["a_replay"] or report["b_world"] or bad) else "FAIL"
    return report


MUTATIONS = {
    "unapproved_entry": lambda d: d["ledger"].append(dict(d["ledger"][0], seq=10 ** 6, key=10 ** 6)),
    "duplicate_key": lambda d: d["ledger"].append(dict(d["ledger"][0], seq=10 ** 6)),
    "payload_change": lambda d: d["ledger"][0].update(amount=d["ledger"][0]["amount"] + 1),
    "after_halt": lambda d: d["gate"]["trace"].insert(0, {"seq": -1, "op": "halt", "caller": d["config"]["admins"][0],
                                                          "args": "{}", "accepted": 1, "result": None, "t": 0}),
    "duplicate_memo": lambda d: d["ledger"].append(dict(d["ledger"][0], seq=10 ** 6, key=10 ** 6 + 1)),
    "over_cap": lambda d: d["config"].update(cap=sum(e["amount"] for e in d["ledger"]) - 1),
}


def self_test(run):
    base = load(run)
    r0 = check(base)
    out = {"base_verdict": r0["verdict"], "mutations": {}}
    if r0["verdict"] != "PASS" or not base["ledger"]:
        out["verdict"] = "FAIL"
        out["why"] = "self-test needs a passing run with a non-empty ledger"
        return out
    for name, mut in MUTATIONS.items():
        d = copy.deepcopy(base)
        mut(d)
        r = check(d)
        out["mutations"][name] = {"verdict": r["verdict"], "c": r["c_reconcile"][:3], "b": r["b_world"][:1]}
    out["verdict"] = "PASS" if all(m["verdict"] == "FAIL" for m in out["mutations"].values()) else "FAIL"
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("run")
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--replay", choices=["both", "interleave", "append"], default="both",
                   help="which model replay decides (a): both (default), or one of them for comparison")
    a = p.parse_args()
    rep = self_test(a.run) if a.self_test else check(load(a.run), a.replay)
    print(json.dumps(rep, indent=2, default=str))
    return 0 if rep["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
