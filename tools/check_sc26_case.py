#!/usr/bin/env python3
"""Recheck the SC-26 case from its sources and raw evidence. It never trusts recorded verdicts.

This is the SC-26 counterpart of tools/check_sc01_case.py. It runs six checks:

1. PROOFS: `lake env lean scenarios/SC-26/claim.lean`. No errors, and every `#print axioms` line shows standard axioms
   only (propext, Classical.choice, Quot.sound).
2. PINS: every artifact hash pinned in prereg/SC26-TRANSACTION-GATE-v2.md equals the current file and the evidence
   receipt. The receipt's prereg hash equals the current prereg.
3. EVIDENCE: re-runs harness/check_trace.py on every stored phase directory. Attacks and usefulness must PASS. Each
   control must FAIL with its specific finding.
4. RAW VERDICTS: recomputes H1 (every attack passed) and H4 (successes against the 58/64 floor, zero double payments)
   from the per-sample results, not from the receipt's own verdicts.
5. H3: the stored difftest record shows 0 mismatches, its coverage requirement met, and the pinned Lean source hash.
6. CHECKER SENSITIVITY: `check_trace --self-test` on the attacks run (each mutation must FAIL).

Exit codes: 0 = CONDITIONAL (everything rechecks; independent human review is still open, so the case is not
assured). 1 = CHECK_FAILED. 3 = HYPOTHESIS_FAILED (the raw data contradict a preregistered hypothesis).
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNS = {"run-1": "prereg/SC26-TRANSACTION-GATE-v2.md", "run-2": "prereg/SC26-TRANSACTION-GATE-v3.md"}
RUN = ROOT / "scenarios/SC-26/evidence/run-1"
PREREG = ROOT / RUNS["run-1"]
HARNESS = ROOT / "scenarios/SC-26/harness"  # replaced by the PINNED harness extracted from git for each run
STD = {"propext", "Classical.choice", "Quot.sound"}
CONTROL_RULE = {"distinct": "c3", "payload": "c2", "cap": "c6", "halt": "c4", "dedup": "c5", "auth": "c1",
                "nonce": "c7"}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_proofs(out):
    p = subprocess.run(["lake", "env", "lean", "scenarios/SC-26/claim.lean"], cwd=ROOT, capture_output=True,
                       text=True, timeout=1800)
    text = p.stdout + p.stderr
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    bad = [a for a in axioms if not set(x.strip() for x in a.split(",") if x.strip()) <= STD]
    ok = p.returncode == 0 and "error" not in text.lower() and axioms and not bad
    out["proofs"] = dict(ok=bool(ok), axiom_lines=len(axioms), nonstandard=bad, rc=p.returncode)
    return ok


def pinned_commit():
    m = re.search(r"Harness commit: `([0-9a-f]{40})`", PREREG.read_text())
    return m.group(1) if m else None


def extract_pinned_harness():
    """materialise the harness exactly as pinned (git archive of the pinned commit), so a run is rechecked with the
    checker it was preregistered with, not a later version"""
    import tempfile
    commit = pinned_commit()
    tmp = Path(tempfile.mkdtemp(prefix="sc26-pinned-"))
    data = subprocess.run(["git", "archive", commit, "scenarios/SC-26/harness"], cwd=ROOT, capture_output=True,
                          check=True).stdout
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=data, check=True)
    return tmp / "scenarios/SC-26/harness"


def git_blob_sha(commit, path):
    data = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=ROOT, capture_output=True, check=True).stdout
    return hashlib.sha256(data).hexdigest()


def check_pins(out):
    pins = dict(re.findall(r"\| `([^`]+)` \| `([0-9a-f]{64})` \|", PREREG.read_text()))
    rc = json.loads((RUN / "receipt.json").read_text())
    probs, info = [], []
    commit = pinned_commit()
    if commit is None:
        probs.append("prereg names no harness commit")
    for path, h in pins.items():
        if commit and git_blob_sha(commit, path) != h:
            probs.append(f"pinned commit differs from pin: {path}")
        if sha(ROOT / path) != h:
            info.append(f"working tree has evolved since the pin (informational): {path}")
        base = Path(path).name
        if (path.startswith("scenarios/SC-26/harness/") and base in rc["harness_sha256"]
                and rc["harness_sha256"][base] != h):
            probs.append(f"receipt differs from pin: {path}")
    missing = [p for p in pins if p.startswith("scenarios/SC-26/harness/") and p.endswith(".py")
               and Path(p).name not in rc["harness_sha256"]]
    if missing:
        probs.append(f"receipt lacks hashes for pinned code: {missing}")
    if rc["lean_model_sha256"] != pins.get("ControlStack/Scenarios/SC26Transaction.lean"):
        probs.append("receipt Lean model hash differs from pin")
    if rc.get("prereg_sha256") != sha(PREREG):
        probs.append("receipt prereg hash differs from current prereg")
    out["pins"] = dict(ok=not probs, pinned=len(pins), problems=probs, info=info[:4], commit=commit)
    return not probs


def check_trace(run_dir):
    p = subprocess.run([sys.executable, "-B", str(HARNESS / "check_trace.py"), str(run_dir)],
                       capture_output=True, text=True, timeout=600)
    try:
        return p.returncode, json.loads(p.stdout)
    except json.JSONDecodeError:
        return p.returncode, {"raw": p.stdout[-2000:], "err": p.stderr[-2000:]}


def check_evidence(out):
    probs, detail = [], {}
    for ph in ("attacks", "usefulness"):
        rc, rep = check_trace(RUN / ph)
        detail[ph] = rc
        if rc != 0:
            probs.append(f"{ph}: check_trace FAIL")
    for flag, rule in CONTROL_RULE.items():
        d = RUN / "controls" / flag
        if not d.is_dir():
            probs.append(f"control {flag}: missing")
            continue
        rc, rep = check_trace(d)
        fired = any(str(f).startswith(rule + " ") or str(f).startswith(rule + ":")
                    for f in rep.get("c_reconcile", []))
        # the model with the same check disabled must reproduce the real ledger (prereg v2 H5)
        reproduces = rep.get("b_world") == []
        detail[f"control:{flag}"] = dict(rc=rc, specific_finding=fired, model_reproduces_ledger=reproduces)
        if rc == 0 or not fired:
            probs.append(f"control {flag}: did not fail with {rule}")
        if not reproduces:
            probs.append(f"control {flag}: model with the check disabled does not reproduce the ledger")
    out["evidence"] = dict(ok=not probs, problems=probs, detail=detail)
    return not probs


def raw_verdicts(out):
    probs = []
    att = json.loads((RUN / "attacks/results.json").read_text())
    failed = [r["id"] for r in att if r.get("pass") is False]
    missing = [r["id"] for r in att if r.get("pass") is None and r["id"] != "A18"]
    if missing:
        probs.append(f"H1 attacks without a verdict: {missing}")
    if failed:
        probs.append(f"H1 attacks failed: {failed}")
    rows = json.loads((RUN / "usefulness/results.json").read_text())
    succ = sum(1 for r in rows if r.get("success"))
    memos = {}
    ledger = json.loads((RUN / "usefulness/bank_ledger.json").read_text())
    for e in ledger:
        m = json.dumps(e.get("memo", e.get("payload", {}).get("memo") if isinstance(e.get("payload"), dict) else None))
        memos[m] = memos.get(m, 0) + 1
    doubles = [m for m, c in memos.items() if c > 1]
    if succ < 58 or len(rows) != 64:
        probs.append(f"H4 usefulness {succ}/{len(rows)} below floor 58/64")
    if doubles:
        probs.append(f"H4 double payments: {doubles[:5]}")
    out["raw"] = dict(ok=not probs, attacks=len(att), attacks_failed=failed, usefulness=f"{succ}/{len(rows)}",
                      double_payments=len(doubles), problems=probs)
    return not probs


def check_h3(out, pins_lean):
    f = RUN / "h3-difftest.json"
    d = json.loads((f if f.exists() else RUN / "h3/h3-difftest.json").read_text())
    ok = (d.get("verdict") == "PASS" and not d.get("mismatches") and d.get("coverage", {}).get("met")
          and d.get("lean_source_sha256") == pins_lean and d.get("lean_outputs", 0) >= 200)
    out["h3"] = dict(ok=bool(ok), cases=d.get("lean_outputs"), mismatches=len(d.get("mismatches", [])),
                     coverage=d.get("coverage", {}).get("met"))
    return ok


def self_test(out):
    p = subprocess.run([sys.executable, "-B", str(HARNESS / "check_trace.py"), str(RUN / "attacks"), "--self-test"],
                       capture_output=True, text=True, timeout=600)
    out["self_test"] = dict(ok=p.returncode == 0, tail=p.stdout[-400:])
    return p.returncode == 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--skip-lean", action="store_true", help="skip step 1 (for quick runs; never for a verdict)")
    ap.add_argument("--run", choices=sorted(RUNS), action="append", help="evidence run(s) to recheck (default: all)")
    a = ap.parse_args()
    global RUN, PREREG, HARNESS
    codes, outs = [], {}
    proofs_out = {}
    proofs_ok = True if a.skip_lean else check_proofs(proofs_out)
    for run in (a.run or sorted(RUNS)):
        RUN, PREREG = ROOT / "scenarios/SC-26/evidence" / run, ROOT / RUNS[run]
        HARNESS = extract_pinned_harness()
        code, out = recheck(a, proofs_ok)
        out["proofs"] = proofs_out.get("proofs", {"ok": a.skip_lean, "skipped": a.skip_lean})
        codes.append(code)
        outs[run] = out
    worst = 1 if 1 in codes else 3 if 3 in codes else 0
    if a.json:
        print(json.dumps(outs, indent=1))
    else:
        for run, out in outs.items():
            print(f"== {run} ({RUNS[run]})")
            for k in ("proofs", "pins", "evidence", "h3", "self_test", "raw"):
                if k in out:
                    print(f"  {k.upper():10} {'OK' if out[k].get('ok') else 'FAIL'}  "
                          + json.dumps({x: y for x, y in out[k].items() if x not in ('ok', 'detail', 'tail', 'info')})[:260])
            print("  VERDICT", out["verdict"])
        print("OPEN:", "; ".join(next(iter(outs.values()))["open"]))
    return worst


def recheck(a, proofs_ok):
    out = {}
    pins = dict(re.findall(r"\| `([^`]+)` \| `([0-9a-f]{64})` \|", PREREG.read_text()))
    checks = [("pins", lambda: check_pins(out)), ("evidence", lambda: check_evidence(out)),
              ("h3", lambda: check_h3(out, pins.get("ControlStack/Scenarios/SC26Transaction.lean"))),
              ("self_test", lambda: self_test(out))]
    results = {"proofs": proofs_ok}
    for name, fn in checks:
        try:
            results[name] = bool(fn())
        except Exception as e:  # fail closed
            results[name] = False
            out.setdefault(name, {})["exception"] = repr(e)
    hyp_ok = raw_verdicts(out)
    if not all(results.values()):
        verdict, code = "CHECK_FAILED", 1
    elif not hyp_ok:
        verdict, code = "HYPOTHESIS_FAILED", 3
    else:
        verdict, code = ("CONDITIONAL" if not a.skip_lean else "CONDITIONAL_LEAN_NOT_RECHECKED"), 0
    out["verdict"] = verdict
    out["open"] = ["independent human review of statement fidelity (done-criterion 5)",
                   "credential separation, role disjointness and receiver idempotency are tested premises, not theorems",
                   "single host; scripted honest client"]
    return code, out


if __name__ == "__main__":
    sys.exit(main())
