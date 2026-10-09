#!/usr/bin/env python3
"""Root-side stack helper for the SC-26 LLM evaluation (run ONLY via `sudo -n /bin/python3 -I stack_helper.py ...`).

Privilege separation: the unprivileged controller (`run_llm_eval.py`, user opc) talks to the model; this helper owns
one fresh SC-26 reference stack (gate, bank, approver directory; reused unchanged from ../harness/run_sc26.py) for ONE
task and executes commands AS THE AGENT UID. It reads newline-delimited JSON from stdin and answers on stdout:

    -> {"cmd": ...}            one grammar command; RE-VALIDATED here against grammar.py, executed as AGENT
    <- {"result": {...}}       the gate/bank reply (or a status summary), exactly what the model will see
    -> {"cmd": "__finish"}     collect the run directory, run check_trace (mediated arms), write helper_report.json
    <- {"finished": true, ...}

Nothing the controller sends is ever executed except a validated grammar command; there is no other code path.
After every mediated command the scripted approver bot (approver.py `policy` mode, APPROVER UID) approves pending
requests whose exact payload is in the task's purchase-order list (each line at most once).

`status` is a read-only summary built by the AUDITOR principal and restricted to the agent's own requests (mediated)
or the agent's own ledger entries (baseline).
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
import run_sc26 as H  # noqa: E402  (the reference stack; not modified)
import grammar as G  # noqa: E402


def tx(c):
    return {"dest": c["dest"], "amount": c["amount"], "memo": c["memo"]}


def status_mediated(st):
    d = st.gate(H.AUDITOR, {"op": "dump"})
    if not d.get("ok"):
        return {"ok": False, "error": "status unavailable"}
    dump = d["result"]
    paid = {e["key"] for e in (st.ledger() or [])}
    approved = {a.get("id") for a in dump.get("approvals", [])}
    reserved = {r.get("id") for r in dump.get("reserved", [])}
    mine = [{"id": r["id"], "dest": r["dest"], "amount": r["amount"], "memo": r["memo"],
             "approved": r["id"] in approved, "executed": r["id"] in reserved, "paid": r["id"] in paid}
            for r in dump.get("requests", []) if r.get("requester") == H.AGENT]
    return {"ok": True, "result": mine}


def status_baseline(st):
    led = st.ledger() or []
    return {"ok": True, "result": [{"key": e["key"], "dest": e["dest"], "amount": e["amount"], "memo": e["memo"]}
                                   for e in led if e.get("caller") == H.AGENT]}


def execute(st, mode, c):
    k = c["cmd"]
    if k == "done":
        return {"ok": True, "result": "done"}
    if k == "status":
        return status_mediated(st) if mode == "mediated" else status_baseline(st)
    if k == "request":
        return st.gate(H.AGENT, {"op": "request", "tx": tx(c)})
    if k == "execute":
        return st.gate(H.AGENT, {"op": "execute", "id": c["id"]})
    if k == "transfer":
        return st.bank(H.AGENT, {"op": "transfer", "key": c["key"], **tx(c)})
    return {"ok": False, "error": "unreachable"}


def chown_tree(root):
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if not (uid and gid):
        return
    for d, dirs, files in os.walk(str(root)):
        for n in [d] + [os.path.join(d, f) for f in dirs + files]:
            os.chown(n, int(uid), int(gid))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["mediated", "baseline"], required=True)
    ap.add_argument("--out", type=Path, required=True, help="task directory (exists, owned by the controller)")
    ap.add_argument("--invoices", required=True, help="JSON list of [dest, amount, memo]")
    a = ap.parse_args()
    if os.geteuid() != 0:
        raise SystemExit("root required (the stack runs each principal under its own UID)")
    run_dir = a.out / "run"
    if not a.out.is_dir() or run_dir.exists():
        raise SystemExit("task directory missing, or run directory already exists")
    invoices = [tuple(x) for x in json.loads(a.invoices)]
    if len(invoices) != 4 or any(len(t) != 3 or any(type(v) is not int or v < 0 for v in t) for t in invoices):
        raise SystemExit("invoices must be 4 triples of naturals")
    grammar = G.GRAMMARS[a.mode]
    cap = sum(t[1] for t in invoices)
    mediated = a.mode == "mediated"
    st = H.Stack(cap=cap, with_gate=mediated, bank_gate_uid=H.GATE if mediated else H.AGENT, crash_hook=False)
    commands, approver_runs = [], []
    try:
        st.start()
        if mediated:
            st.set_po(invoices)
        print(json.dumps({"ready": True, "mode": a.mode, "cap": cap, "agent_uid": H.AGENT}), flush=True)
        for line in sys.stdin:
            try:
                msg = json.loads(line)
            except ValueError:
                msg = None
            if isinstance(msg, dict) and msg.get("cmd") == "__finish" and set(msg) == {"cmd"}:
                break
            try:
                c = G.validate(msg, grammar)
                reply = execute(st, a.mode, c)
            except G.Invalid as e:
                c, reply = None, {"ok": False, "error": "invalid command: " + str(e)}
            commands.append({"cmd": c, "reply": reply})
            if mediated and c is not None and c["cmd"] in ("request", "execute"):
                approver_runs.append(st.approver("policy", "--po", str(st.po)))
            print(json.dumps({"result": reply}, sort_keys=True), flush=True)
        ledger = st.ledger() or []
        st.collect(run_dir, {"phase": "llm_eval", "mode": a.mode, "invoices": [list(t) for t in invoices]})
    finally:
        st.cleanup()
    check = H.check_run(run_dir) if mediated else None
    report = {"mode": a.mode, "invoices": [list(t) for t in invoices], "cap": cap, "ledger": ledger,
              "commands_executed": commands, "approver_runs": approver_runs,
              "check_trace_verdict": check["verdict"] if check else None,
              "check_trace_findings": ({"a": check.get("a_replay"), "b": check.get("b_world"),
                                        "c": check.get("c_reconcile")} if check else None)}
    (a.out / "helper_report.json").write_text(json.dumps(report, indent=1, default=str))
    chown_tree(a.out)
    print(json.dumps({"finished": True, "check_trace": report["check_trace_verdict"], "ledger_n": len(ledger)}),
          flush=True)


if __name__ == "__main__":
    main()
