"""Re-gate all saved comparisons and witnesses; write only JSON receipts.

Run from the repository root:
    python3 docs/lean-english/one-to-one/blind-g0n1/regate.py

No previous receipts or gate temporary directory are required. The deterministic
helper assembles fresh checks and removes them after Lean finishes.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("blind_runner", OUT / "run_gate_blind.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    canonical = OUT.parent / "leangate_imports.py"
    helper_matches = Path(g.__file__).read_bytes() == canonical.read_bytes()
    def run_one(n):
        all_ok = True
        cid = f"bg0n1_{n}"
        sp = OUT / f"{cid}.statement.lean"
        pp = OUT / f"{cid}.proof.lean"
        statement = sp.read_text() if sp.exists() else ""
        proof = pp.read_text() if pp.exists() else ""
        if not helper_matches:
            checked, statement_log = False, "Gate helper differs from the authorized helper"
        elif not sp.exists() or not pp.exists():
            checked, statement_log = False, "Missing saved statement or proof"
        else:
            checked, statement_log = g.check_statement(cid, statement, [runner.IMPORTS])
        for target in ("claim", "witness"):
            if checked:
                ok, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            else:
                ok, log = False, statement_log
            receipt = {
                "passed": ok,
                "target": target,
                "statement_passed": checked,
                "statement_sha256": digest(statement.encode()),
                "proof_sha256": digest(proof.encode()),
                "gate_sha256": digest(Path(g.__file__).read_bytes()),
                "trusted_header": runner.IMPORTS,
                "PL_IMPORTS": os.environ["PL_IMPORTS"],
                "PL_LEAN_PROJ": str(runner.ROOT),
                "gate_unmodified": False,
                "security_checks_unchanged": helper_matches,
                "imports_option_local_only": True,
                "statement_log": statement_log,
                "gate_log": log,
            }
            suffix = ".receipt.json" if target == "claim" else ".witness.receipt.json"
            (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + "\n")
            print(f"{cid} {target}: {'PASS' if ok else 'FAIL'} {log[:180]}", flush=True)
            all_ok = all_ok and ok
        return all_ok
    # Claims are independent. Each invocation still uses the unchanged gate,
    # with fresh nonce-bearing check files and a separate axiom audit.
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run_one, range(1, 11)))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
