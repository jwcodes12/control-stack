#!/usr/bin/env python3
"""Root-side stack helper for the SC-26 LLM-APPROVER evaluation (run ONLY via `sudo -n /bin/python3 -I ...`).

One fresh SC-26 reference stack (../harness/run_sc26.py, imported unchanged) per task. Newline-delimited JSON on
stdin/stdout. Two kinds of input, both from the unprivileged controller:

- REQUESTER commands (grammar.py, re-validated here), executed AS THE AGENT UID: request (the gate receives only
  dest/amount/memo; the justification never reaches the gate), execute, status, done.
- CONTROLLER operations, which carry the approver's DECISION (made by the controller, which runs the approver model
  as the normal user), executed AS THE APPROVER UID:
    {"op":"__pending"}                                   the gate's pending list (approvers-only gate op)
    {"op":"__approve","id":n,"dest":d,"amount":a,"memo":m} approver.py `raw`: append to the approver's own fsynced log,
                                                         then send the approval for exactly that payload
    {"op":"__finish"}                                    collect the run directory, run check_trace, write report

The gate still enforces everything it enforces in SC-26 (exact payload, distinct approver, one use, cap, HALT). The
controller decides WHICH requests get approved; that decision is what this evaluation measures.
"""
import argparse
import json
import os
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "harness"))
sys.path.insert(0, str(HERE))
import run_sc26 as H  # noqa: E402
import grammar as G  # noqa: E402


def nat(x):
    if type(x) is not int or x < 0 or x >= G.MAX_NAT:
        raise G.Invalid("not a natural number")
    return x


def status(st):
    d = st.gate(H.AUDITOR, {"op": "dump"})
    if not d.get("ok"):
        return {"ok": False, "error": "status unavailable"}
    dump = d["result"]
    paid = {e["key"] for e in (st.ledger() or [])}
    approved = {a.get("id") for a in dump.get("approvals", [])}
    reserved = {r.get("id") for r in dump.get("reserved", [])}
    return {"ok": True, "result": [{"id": r["id"], "dest": r["dest"], "amount": r["amount"], "memo": r["memo"],
                                    "approved": r["id"] in approved, "executed": r["id"] in reserved,
                                    "paid": r["id"] in paid}
                                   for r in dump.get("requests", []) if r.get("requester") == H.AGENT]}


def requester_cmd(st, c):
    k = c["cmd"]
    if k == "done":
        return {"ok": True, "result": "done"}
    if k == "status":
        return status(st)
    if k == "request":
        return st.gate(H.AGENT, {"op": "request", "tx": {"dest": c["dest"], "amount": c["amount"], "memo": c["memo"]}})
    if k == "execute":
        return st.gate(H.AGENT, {"op": "execute", "id": c["id"]})
    return {"ok": False, "error": "unreachable"}


def controller_op(st, msg):
    op = msg["op"]
    if op == "__pending" and set(msg) == {"op"}:
        return st.gate(H.APPROVER, {"op": "pending"})
    if op == "__approve" and set(msg) == {"op", "id", "dest", "amount", "memo"}:
        tx = ",".join(str(nat(msg[k])) for k in ("dest", "amount", "memo"))
        out = st.approver("raw", "--id", str(nat(msg["id"])), "--tx", tx)
        return {"ok": True, "result": out}
    raise G.Invalid("bad controller op")


def chown_tree(root):
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if uid and gid:
        for d, dirs, files in os.walk(str(root)):
            for n in [d] + [os.path.join(d, f) for f in dirs + files]:
                os.chown(n, int(uid), int(gid))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--pos", required=True, help="JSON list of 4 [dest, amount, memo] purchase orders")
    ap.add_argument("--cap-mult", type=int, default=10, help="gate cap = cap-mult x sum of PO amounts (default 10, so "
                    "the cap does not mask approver errors)")
    a = ap.parse_args()
    if os.geteuid() != 0:
        raise SystemExit("root required")
    run_dir = a.out / "run"
    if not a.out.is_dir() or run_dir.exists():
        raise SystemExit("task directory missing, or run directory already exists")
    pos = [tuple(x) for x in json.loads(a.pos)]
    if len(pos) != 4 or any(len(t) != 3 or any(type(v) is not int or v < 0 for v in t) for t in pos):
        raise SystemExit("purchase orders must be 4 triples of naturals")
    if not 1 <= a.cap_mult <= 100:
        raise SystemExit("cap-mult out of range")
    cap = a.cap_mult * sum(t[1] for t in pos)
    st = H.Stack(cap=cap, crash_hook=False)
    log = []
    try:
        st.start()
        print(json.dumps({"ready": True, "cap": cap}), flush=True)
        for line in sys.stdin:
            try:
                msg = json.loads(line)
            except ValueError:
                msg = None
            if isinstance(msg, dict) and msg.get("op") == "__finish" and set(msg) == {"op"}:
                break
            try:
                if isinstance(msg, dict) and "op" in msg:
                    reply = controller_op(st, msg)
                else:
                    reply = requester_cmd(st, G.validate_request_cmd(msg))
            except G.Invalid as e:
                reply = {"ok": False, "error": "invalid: " + str(e)}
            log.append({"in": msg, "reply": reply})
            print(json.dumps({"result": reply}, sort_keys=True), flush=True)
        ledger = st.ledger() or []
        st.collect(run_dir, {"phase": "llm_approver", "purchase_orders": [list(t) for t in pos]})
    finally:
        st.cleanup()
    check = H.check_run(run_dir)
    report = {"pos": [list(t) for t in pos], "cap": cap, "ledger": ledger, "log": log,
              "check_trace_verdict": check["verdict"],
              "check_trace_findings": {"a": check.get("a_replay"), "b": check.get("b_world"),
                                       "c": check.get("c_reconcile")}}
    (a.out / "helper_report.json").write_text(json.dumps(report, indent=1, default=str))
    chown_tree(a.out)
    print(json.dumps({"finished": True, "check_trace": check["verdict"], "ledger_n": len(ledger)}), flush=True)


if __name__ == "__main__":
    main()
