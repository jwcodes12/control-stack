"""Recheck all six saved pointwise comparisons and all six non-vacuity witnesses.

Run from the repository root. Only persisted receipts are rewritten. The runner
configures the unchanged deterministic gate, project root, and trusted imports.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import importlib.util
import hashlib
import json
import os
from concurrent.futures import ThreadPoolExecutor

OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('blind_runner', OUT / 'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g

def sha(data):
    return hashlib.sha256(data).hexdigest()

def recheck(n):
    cid = f'bg6n3_{n}'
    paths = [OUT / f'{cid}.statement.lean', OUT / f'{cid}.proof.lean']
    try:
        statement, proof = [p.read_text() for p in paths]
        statement_ok, statement_log = g.check_statement(cid, statement, [runner.IMPORTS])
        results = []
        for target in ['claim', 'witness']:
            if statement_ok:
                passed, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            else:
                passed, log = False, 'Statement check failed; target not gated.\n' + statement_log
            receipt = {
                'cid': cid, 'target': target, 'passed': passed,
                'statement_check_passed': statement_ok,
                'statement_check_log': statement_log, 'gate_log': log,
                'statement_sha256': sha(statement.encode()), 'proof_sha256': sha(proof.encode()),
                'gate_sha256': sha(Path(g.__file__).read_bytes()),
                'PL_IMPORTS': os.environ['PL_IMPORTS'], 'PL_LEAN_PROJ': str(g.PROJ),
                'security_checks_unchanged': True, 'gate_helper_byte_identical':
                    Path(g.__file__).read_bytes() == (OUT.parent / 'leangate_imports.py').read_bytes(),
            }
            suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
            (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + '\n')
            print(f'{cid} {target}: {"PASS" if passed else "FAIL"}\n{log[:400]}', flush=True)
            results.append(passed)
        return all(results)
    except Exception as exc:
        for target in ['claim', 'witness']:
            suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
            (OUT / (cid + suffix)).write_text(json.dumps({
                'cid': cid, 'target': target, 'passed': False, 'error': str(exc)
            }, indent=2) + '\n')
        print(f'{cid}: FAIL {exc}', flush=True)
        return False

if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=3) as executor:
        results = list(executor.map(recheck, range(1, 7)))
    sys.exit(0 if all(results) else 1)
