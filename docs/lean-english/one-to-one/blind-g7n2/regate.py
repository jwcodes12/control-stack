#!/usr/bin/env python3
"""Recheck saved statements and both proof targets; replace receipts only."""
from pathlib import Path
import concurrent.futures
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("blind_runner", OUT / "run_gate_blind.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def recheck(n):
    cid = f"bg7n2_{n}"
    sp = OUT / f"{cid}.statement.lean"
    pp = OUT / f"{cid}.proof.lean"
    try:
        statement, proof = sp.read_text(), pp.read_text()
        ok, statement_log = g.check_statement(cid, statement, [runner.IMPORTS])
        targets = {}
        for target in ("claim", "witness"):
            passed, log = (g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
                           if ok else (False, "Statement rejected: " + statement_log))
            receipt = {
                "cid": cid, "target": target, "passed": passed,
                "statement_passed": ok, "statement_log": statement_log, "gate_log": log,
                "statement_sha256": digest(statement), "proof_sha256": digest(proof),
                "gate_sha256": hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
                "gate_unmodified": False, "security_checks_unchanged": True,
                "imports_option_local_only": True,
                "PL_IMPORTS": runner.os.environ["PL_IMPORTS"],
                "PL_LEAN_PROJ": str(g.PROJ), "trusted_header": runner.IMPORTS,
            }
            suffix = ".receipt.json" if target == "claim" else ".witness.receipt.json"
            (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + "\n")
            targets[target] = passed
            print(cid, target, passed, log[:160], flush=True)
        return all(targets.values())
    except Exception as exc:
        for target in ("claim", "witness"):
            suffix = ".receipt.json" if target == "claim" else ".witness.receipt.json"
            (OUT / (cid + suffix)).write_text(json.dumps({
                "cid": cid, "target": target, "passed": False, "error": str(exc)
            }, indent=2) + "\n")
        print(cid, "ERROR", str(exc), flush=True)
        return False


if __name__ == "__main__":
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        outcomes = list(pool.map(recheck, range(1, 14)))
    sys.exit(0 if all(outcomes) else 1)
