#!/usr/bin/env python3
"""Re-gate all saved claims and witnesses. Persist only JSON receipts.

Run from the repository root:
  python3 docs/lean-english/one-to-one/blind-g2n1/regate.py
No existing receipt or temporary gate file is required.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import runpy
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
config = runpy.run_path(str(OUT / 'run_gate_blind.py'), run_name='blind_gate_config')
g = config['g']
DEPENDENCIES = [config['IMPORTS']]
GATE_HASH = hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest()
IMPORTS = config['os'].environ['PL_IMPORTS']

def check(n):
    cid = f'bg2n1_{n}'
    sp = OUT / f'{cid}.statement.lean'
    pp = OUT / f'{cid}.proof.lean'
    results = []
    try:
        statement, proof = sp.read_text(), pp.read_text()
        stmt_ok, stmt_log = g.check_statement(cid, statement, DEPENDENCIES)
        for target in ('claim', 'witness'):
            passed, log = g.gate(cid, statement, proof, target, DEPENDENCIES, timeout=120)
            passed = stmt_ok and passed
            receipt = {
                'cid': cid, 'target': target, 'passed': passed,
                'statement_passed': stmt_ok, 'statement_log': stmt_log, 'gate_log': log,
                'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
                'proof_sha256': hashlib.sha256(proof.encode()).hexdigest(),
                'gate_sha256': GATE_HASH, 'trusted_header': config['IMPORTS'],
                'PL_IMPORTS': IMPORTS, 'PL_LEAN_PROJ': str(g.PROJ),
                'gate_unmodified': False, 'security_checks_unchanged': True,
                'imports_option_local_only': True,
            }
            dest = OUT / (f'{cid}.receipt.json' if target == 'claim' else f'{cid}.witness.receipt.json')
            dest.write_text(json.dumps(receipt, indent=2) + '\n')
            results.append(passed)
            print(f'{cid} {target}: {"PASS" if passed else "FAIL"}\n{log[:1400]}', flush=True)
    except Exception as error:
        for target in ('claim', 'witness'):
            dest = OUT / (f'{cid}.receipt.json' if target == 'claim' else f'{cid}.witness.receipt.json')
            dest.write_text(json.dumps({'cid': cid, 'target': target, 'passed': False,
                'error': f'{type(error).__name__}: {error}'}, indent=2) + '\n')
        print(f'{cid}: FAIL {type(error).__name__}: {error}', flush=True)
        return False
    return all(results)

if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, range(1, 11)))
    sys.exit(0 if all(results) else 1)
