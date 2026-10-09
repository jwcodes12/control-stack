#!/usr/bin/env python3
"""Differential test: model.py against Lean's own evaluation of `ControlStack.SC26.run`.

Random legal traces (fixed seed `SEED`, printed) are evaluated by model.py and by Lean `#eval` under the full checks and under
each single-check negative control. The generated Lean file is the VERBATIM source of
ControlStack/Scenarios/SC26Transaction.lean (so no prebuilt .olean of it is needed, and the definitions evaluated
are exactly the ones the theorems are about) followed by a `canon` printer and the `#eval`s. Pass = every canonical
final state is identical AND coverage holds: at least half the traces contain an `arrive` that adds a bank entry,
and every operation constructor is accepted (its `guard` holds) at least 10 times overall. Run from anywhere; needs the repository's Lake environment (Mathlib + Core.Gate built).
"""
import argparse
import hashlib
import json
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "ControlStack/Scenarios/SC26Transaction.lean"
sys.path.insert(0, str(HERE))
import model as M  # noqa: E402
from test_model import R  # noqa: E402

SEED = 2626  # fixed; printed in the report
AG, AG2, AP, AD, GATE = 1, 2, 3, 4, 9

CANON = r'''
namespace SC26Diff
open ControlStack.SC26
def txK (t : Tx) : String := s!"({t.dest},{t.amount},{t.memo})"
def canon (s : St) : String :=
  "n=" ++ toString s.next ++
  "|r=" ++ ";".intercalate (s.reqs.map fun r => s!"{r.id}:{r.requester}:{txK r.tx}") ++
  "|a=" ++ ";".intercalate (s.approvals.map fun a => s!"{a.1}:{a.2.1}:{txK a.2.2}") ++
  "|v=" ++ ";".intercalate (s.reserved.map toString) ++
  "|s=" ++ toString s.spent ++
  "|h=" ++ (if s.halted then "1" else "0") ++
  "|b=" ++ ";".intercalate (s.bank.map fun e => s!"{e.1}:{txK e.2}") ++
  "|m=" ++ ";".intercalate (s.net.map fun e => s!"{e.1}:{txK e.2}")
end SC26Diff
open ControlStack.SC26 in
'''

FLAGS = ["distinct", "payload", "nonce", "cap", "haltCheck", "bankDedup", "bankAuth"]
OPS = ["request", "approve", "execute", "deliver", "arrive", "bankCall", "halt"]


def advance(s, rng):
    """the next honest step for some request: approve, execute, send, or let a sent message arrive"""
    bank_keys = {e[0] for e in s.bank}
    steps = []
    for r in s.reqs:
        if not any(a[0] == r.id for a in s.approvals):
            steps.append(M.approve(AP, r.id, tuple(r.tx)))
        elif r.id not in s.reserved:
            steps.append(M.execute(r.requester, r.id))
        elif not any(m[0] == r.id for m in s.net):
            steps.append(M.deliver(r.id))
        elif r.id not in bank_keys:
            steps.append(M.arrive(r.id))
    return rng.choice(steps) if steps else None


def gen_trace(rng, C, cap):
    """a random LEGAL trace, biased toward the happy path so that arrivals reach the bank, with noise in every
    constructor; generated against the model under the same checks `C`"""
    txs = [(rng.randrange(4), rng.randrange(1, 8), rng.randrange(3)) for _ in range(3)]
    n = rng.randrange(8, 50)
    s, ops = M.INIT, []
    for k in range(n):
        u = rng.random()
        ids = [r.id for r in s.reqs]
        pick = lambda xs: rng.choice(xs) if xs and rng.random() < .85 else rng.randrange(6)
        adv = advance(s, rng) if rng.random() < .5 else None
        if adv is not None:
            o = adv
        elif k > .85 * n and rng.random() < .25:
            o = M.halt(rng.choice([AD, AD, AG, AP]))
        elif u < .15:
            o = M.request(rng.choice([AG, AG2, AG2, AP, 5]), rng.choice(txs))
        elif u < .35:
            unapproved = [i for i in ids if not any(a[0] == i for a in s.approvals)]
            i = pick(unapproved or ids)
            r = M.req_of(s, i)
            tx = r.tx if r is not None and rng.random() < .85 else rng.choice(txs)
            o = M.approve(rng.choice([AP, AP, AP, AP, AG, AD]), i, tx)
        elif u < .55:
            fresh = sorted({a[0] for a in s.approvals} - set(s.reserved))
            o = M.execute(rng.choice([AG, AG2, AP, 5]), pick(fresh or sorted({a[0] for a in s.approvals})))
        elif u < .7:
            o = M.deliver(pick(list(s.reserved)))
        elif u < .9:
            unpaid = [m[0] for m in s.net if m[0] not in [e[0] for e in s.bank]]
            o = M.arrive(pick(unpaid or [m[0] for m in s.net]))
        else:
            o = M.bankCall(rng.choice([AG, AP, AD, 5]), rng.randrange(6), rng.choice(txs))
        assert M.legal(R, o)
        ops.append(o)
        s = M.step(R, cap, C, s, o)
    return ops


def coverage(cases):
    acc = {k: 0 for k in OPS}
    adding = 0
    for cap, C, ops, _ in cases:
        s, added = M.INIT, False
        for o in ops:
            if M.guard(R, cap, C, s, o):
                acc[o[0]] += 1
            t = M.step(R, cap, C, s, o)
            if o[0] == "arrive" and len(t.bank) > len(s.bank):
                added = True
            s = t
        adding += added
    return acc, adding


def checks_lean(C):
    return "(⟨" + ", ".join("true" if getattr(C, f) else "false" for f in FLAGS) + "⟩ : ControlStack.SC26.Checks)"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=200)
    ap.add_argument("--seed", type=int, default=SEED)
    ap.add_argument("--json", type=Path)
    a = ap.parse_args()
    src = LEAN.read_text()
    if re.search(r"\bsorry\b", src):
        print("FAIL: Lean source contains sorry")
        return 1
    rng = random.Random(a.seed)
    cases = []
    for i in range(a.n):
        cap = rng.randrange(5, 40)
        C = M.FULL if i % 2 == 0 else M.FULL._replace(**{FLAGS[(i // 2) % 7]: False})
        ops = gen_trace(rng, C, cap)
        cases.append((cap, C, ops, M.state_to_key(M.run(R, cap, C, M.INIT, ops))))
    body = []
    rl = M.roles_to_lean(R).replace(": Roles)", ": ControlStack.SC26.Roles)")
    for i, (cap, C, ops, _) in enumerate(cases):
        lops = M.to_lean(ops).replace("Op.", "ControlStack.SC26.Op.")
        body.append(f'#eval IO.println ("CASE {i} " ++ SC26Diff.canon (ControlStack.SC26.run {rl} {cap} '
                    f'{checks_lean(C)} ControlStack.SC26.init {lops}))')
    text = src + "\n" + CANON.replace("open ControlStack.SC26 in\n", "") + "\n".join(body) + "\n"
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "SC26Diff.lean"
        f.write_text(text)
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO, capture_output=True, text=True, timeout=1800)
    out = {}
    for line in p.stdout.splitlines():
        m = re.match(r"CASE (\d+) (.*)$", line)
        if m:
            out[int(m.group(1))] = m.group(2)
    errors = [l for l in p.stdout.splitlines() if ": error" in l][:5]
    mism = [i for i, c in enumerate(cases) if out.get(i) != c[3]]
    acc, adding = coverage(cases)
    cov_ok = adding * 2 >= len(cases) and all(v >= 10 for v in acc.values())
    res = {"seed": a.seed, "lean_source_sha256": hashlib.sha256(src.encode()).hexdigest(), "cases": len(cases),
           "coverage": {"traces_with_bank_adding_arrive": adding, "accepted_per_constructor": acc,
                        "required": ">= 50% of traces with a bank-adding arrive; every constructor accepted >= 10",
                        "met": cov_ok},
           "lean_outputs": len(out), "mismatches": mism[:20], "lean_errors": errors, "lean_rc": p.returncode,
           "control_cases": sum(1 for c in cases if c[1] != M.FULL)}
    if mism:
        i = mism[0]
        res["first_mismatch"] = {"python": cases[i][3], "lean": out.get(i), "ops": M.to_lean(cases[i][2])}
    res["verdict"] = "PASS" if p.returncode == 0 and not mism and len(out) == len(cases) and cov_ok else "FAIL"
    print(json.dumps(res, indent=1))
    if a.json:
        a.json.write_text(json.dumps(res, indent=1))
    return 0 if res["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
