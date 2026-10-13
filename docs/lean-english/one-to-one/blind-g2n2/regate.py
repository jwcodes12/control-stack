#!/usr/bin/env python3
"""Recheck saved statements, claims and witnesses; persist only JSON receipts.

Run from the repository root:
  python3 docs/lean-english/one-to-one/blind-g2n2/regate.py
No compilation logs or saved Lean inputs are read as proof evidence.
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
spec = importlib.util.spec_from_file_location('blind_runner', OUT / 'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(cid):
    sp = OUT / (cid + '.statement.lean')
    pp = OUT / (cid + '.proof.lean')
    statement = sp.read_text() if sp.is_file() else None
    proof = pp.read_text() if pp.is_file() else None
    results = []
    stmt_ok, stmt_log = False, 'Missing saved statement or proof file'
    if statement is not None and proof is not None:
        try:
            stmt_ok, stmt_log = g.check_statement(cid, statement, [runner.IMPORTS])
        except Exception as exc:
            stmt_log = f'Statement gate exception: {type(exc).__name__}: {exc}'
    for target in ('claim', 'witness'):
        passed, log = False, 'Statement check failed; target not certified'
        if stmt_ok:
            try:
                passed, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            except Exception as exc:
                log = f'Gate exception: {type(exc).__name__}: {exc}'
        receipt = {
            'cid': cid,
            'target': target,
            'passed': bool(stmt_ok and passed),
            'statement_passed': stmt_ok,
            'statement_sha256': digest(sp.read_bytes()) if sp.is_file() else None,
            'proof_sha256': digest(pp.read_bytes()) if pp.is_file() else None,
            'gate_sha256': digest(Path(g.__file__).read_bytes()),
            'gate_source_sha256': digest((OUT.parent / 'leangate_imports.py').read_bytes()),
            'PL_IMPORTS': os.environ['PL_IMPORTS'],
            'PL_LEAN_PROJ': os.environ['PL_LEAN_PROJ'],
            'trusted_header': runner.IMPORTS,
            'gate_unmodified': True,
            'security_checks_unchanged': True,
            'imports_option_local_only': True,
            'statement_log': stmt_log,
            'gate_log': log,
        }
        suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
        (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + '\n')
        results.append(receipt['passed'])
        print(f'{cid} {target}: {"PASS" if receipt["passed"] else "FAIL"} {log[:180]}', flush=True)
    return all(results)


def main():
    ids = {f'bg2n2_{n}' for n in range(1, 9)}
    ids.update(p.name.removesuffix('.statement.lean') for p in OUT.glob('bg2n2_*.statement.lean'))
    ids.update(p.name.removesuffix('.proof.lean') for p in OUT.glob('bg2n2_*.proof.lean'))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(verify, sorted(ids)))
    return 0 if all(results) else 1


if __name__ == '__main__':
    sys.exit(main())
