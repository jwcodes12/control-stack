"""From the repository root: python3 docs/lean-english/one-to-one/blind-g3n1/regate.py.

Recheck all ten saved statements, claims and witnesses. Only receipts are
persistently rewritten; the unchanged deterministic gate removes its scratch files.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import importlib.util
import hashlib
import json
import os
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('blind_runner', OUT/'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g

def sha(data):
    return hashlib.sha256(data).hexdigest()

def check(n):
    cid = f'bg3n1_{n}'
    sf, pf = OUT/f'{cid}.statement.lean', OUT/f'{cid}.proof.lean'
    timestamp = datetime.now(timezone.utc).isoformat()
    base = {
        'cid': cid, 'utc': timestamp,
        'project': os.environ['PL_LEAN_PROJ'],
        'PL_IMPORTS': os.environ['PL_IMPORTS'],
        'trusted_header': runner.IMPORTS,
        'gate_sha256': sha(Path(g.__file__).read_bytes()),
        'runner_sha256': sha((OUT/'run_gate_blind.py').read_bytes()),
        'gate_unmodified': False, 'security_checks_unchanged': True,
        'imports_option_local_only': True,
    }
    try:
        statement, proof = sf.read_text(), pf.read_text()
        base.update(statement_sha256=sha(statement.encode()), proof_sha256=sha(proof.encode()))
        stmt_ok, stmt_log = g.check_statement(cid, statement, [runner.IMPORTS])
        base.update(statement_passed=stmt_ok, statement_log=stmt_log)
    except Exception as exc:
        statement = proof = ''
        stmt_ok, stmt_log = False, f'{type(exc).__name__}: {exc}'
        base.update(statement_passed=False, statement_log=stmt_log)
    passed = True
    for target in ['claim', 'witness']:
        if stmt_ok:
            try:
                ok, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            except Exception as exc:
                ok, log = False, f'{type(exc).__name__}: {exc}'
        else:
            ok, log = False, stmt_log
        suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
        (OUT/(cid+suffix)).write_text(json.dumps({**base, 'target': target, 'passed': ok, 'log': log}, indent=2)+'\n')
        print(cid, target, 'PASS' if ok else 'FAIL', log[:500], flush=True)
        passed = passed and ok
    return passed

def main():
    expected = {f'bg3n1_{n}.statement.lean' for n in range(1, 11)}
    actual = {p.name for p in OUT.glob('bg3n1_*.statement.lean')}
    inventory_ok = actual == expected
    if not inventory_ok:
        print('FAIL statement inventory:', sorted(expected-actual), sorted(actual-expected), flush=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(check, range(1, 11)))
    return 0 if inventory_ok and all(results) else 1

if __name__ == '__main__':
    sys.exit(main())
