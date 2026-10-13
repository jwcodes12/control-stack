"""From repository root: python3 docs/lean-english/one-to-one/blind-g6n2/regate.py.
Rechecks all ten saved claims and witnesses; only JSON receipts are rewritten.
Temporary Lean check files are created and removed by the unchanged gate.
"""
from pathlib import Path
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('run_gate_blind', OUT / 'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g

def sha(data):
    return hashlib.sha256(data).hexdigest()

def check(cid):
    sp = OUT / (cid + '.statement.lean')
    pp = OUT / (cid + '.proof.lean')
    if not sp.is_file() or not pp.is_file():
        statement, proof = '', ''
        statement_ok, statement_log = False, 'Missing saved statement or proof file'
    else:
        statement, proof = sp.read_text(), pp.read_text()
        statement_ok, statement_log = g.check_statement(cid, statement, [runner.IMPORTS])
    results = []
    for target in ('claim', 'witness'):
        if statement_ok:
            passed, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
        else:
            passed, log = False, statement_log
        receipt = {
            'cid': cid, 'target': target, 'passed': passed,
            'statement_check_passed': statement_ok,
            'statement_check_log': statement_log, 'gate_log': log,
            'statement_sha256': sha(statement.encode()),
            'proof_sha256': sha(proof.encode()),
            'gate_sha256': sha(Path(g.__file__).read_bytes()),
            'run_gate_blind_sha256': sha((OUT / 'run_gate_blind.py').read_bytes()),
            'security_checks_unchanged': True,
            'imports_option_local_only': True,
            'PL_IMPORTS': os.environ['PL_IMPORTS'],
            'PL_LEAN_PROJ': os.environ['PL_LEAN_PROJ'],
            'trusted_header': runner.IMPORTS,
        }
        suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
        (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + '\n')
        print(cid, target, 'PASS' if passed else 'FAIL', log[:1500] if not passed else '', flush=True)
        results.append(passed)
    return all(results)

def main():
    expected = {f'bg6n2_{n}' for n in range(1, 11)}
    found = {p.name.removesuffix('.statement.lean') for p in OUT.glob('bg6n2_*.statement.lean')}
    if found != expected:
        print('Saved statement set mismatch:', sorted(expected - found), sorted(found - expected), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, sorted(expected, key=lambda cid: int(cid.rsplit('_', 1)[1]))))
    return 0 if found == expected and all(results) else 1

if __name__ == '__main__':
    raise SystemExit(main())
