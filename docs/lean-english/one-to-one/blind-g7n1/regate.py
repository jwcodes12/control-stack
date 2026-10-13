#!/usr/bin/env python3
"""Re-gate saved claims and witnesses; persistent writes are receipts only."""
from pathlib import Path
import concurrent.futures
import datetime
import hashlib
import importlib.util
import json
import os
import sys
import tempfile

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    if Path.cwd().resolve() != ROOT:
        print('Run this script from the repository root.', file=sys.stderr)
        return 1
    original_gate = OUT.parent / 'leangate_imports.py'
    if digest(original_gate) != digest(OUT / 'leangate_imports.py'):
        print('The copied deterministic gate differs from the authorized helper.', file=sys.stderr)
        return 1
    expected = {f'bg7n1_{n}' for n in range(1, 11)}
    found = {p.name.removesuffix('.statement.lean') for p in OUT.glob('bg7n1_*.statement.lean')}
    if found != expected:
        print(f'Claim file inventory mismatch: {sorted(found ^ expected)}', file=sys.stderr)
        return 1
    for p, expected_hash in json.loads((OUT / 'typed/HASHES.json').read_text())['files'].items():
        if digest(OUT / 'typed' / p) != expected_hash:
            print('Frozen typed file changed: ' + p, file=sys.stderr)
            return 1
    frozen = json.loads((OUT / 'COMPARISON-HASHES.json').read_text()) if (OUT / 'COMPARISON-HASHES.json').exists() else None
    if frozen:
        for p, expected_hash in frozen['files'].items():
            if digest(OUT / p) != expected_hash:
                print('Frozen comparison file changed: ' + p, file=sys.stderr)
                return 1
    # Build missing project dependencies offline in a disposable directory. This
    # also makes a clean checkout independent of the typing-stage import cache.
    with tempfile.TemporaryDirectory(prefix='regate-', dir=OUT) as tmp:
        prep = load_module('blind_prepare_imports', OUT / 'prepare_imports.py')
        env = prep.prepare(cache=Path(tmp) / 'imports', record=False)
        os.environ['LEAN_PATH'] = env['LEAN_PATH']
        wrapper = load_module('blind_wrapper', OUT / 'run_gate_blind.py')
        gate = wrapper.g
        gate.GATE_DIR = Path(tmp) / 'gate'

        def run(cid):
            statement_path = OUT / (cid + '.statement.lean')
            proof_path = OUT / (cid + '.proof.lean')
            statement = statement_path.read_text()
            proof = proof_path.read_text()
            st_ok, st_log = gate.check_statement(cid, statement, [wrapper.IMPORTS])
            results = {}
            for target in ('claim', 'witness'):
                if st_ok:
                    passed, log = gate.gate(cid, statement, proof, target, [wrapper.IMPORTS], timeout=120)
                else:
                    passed, log = False, 'Statement check failed: ' + st_log
                results[target] = dict(passed=passed, log=log)
            base = dict(cid=cid, checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        statement_passed=st_ok, statement_sha256=digest(statement_path),
                        proof_sha256=digest(proof_path), gate_sha256=digest(original_gate),
                        gate_unmodified=False, security_checks_unchanged=True,
                        imports_option_local_only=True, trusted_header=wrapper.IMPORTS,
                        pl_imports=os.environ['PL_IMPORTS'], pl_lean_proj=str(ROOT),
                        gate_helper_byte_identical=True)
            (OUT / (cid + '.statement-check.txt')).write_text(st_log + '\n')
            for target, suffix in [('claim', ''), ('witness', '.witness')]:
                result = results[target]
                receipt = {**base, 'target': target, 'passed': st_ok and result['passed']}
                log_name = cid + ('.gate.txt' if target == 'claim' else '.witness-gate.txt')
                (OUT / log_name).write_text(result['log'] + '\n')
                (OUT / (cid + suffix + '.receipt.json')).write_text(json.dumps(receipt, indent=2) + '\n')
            passed = st_ok and all(result['passed'] for result in results.values())
            print(cid, 'PASS' if passed else 'FAIL', flush=True)
            if not passed:
                for target, result in results.items():
                    if not result['passed']:
                        print(target, result['log'][:3500], flush=True)
            return passed

        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            passed = list(pool.map(run, sorted(expected, key=lambda cid: int(cid.rsplit('_', 1)[1]))))
    return 0 if all(passed) else 1

if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        print(f'Re-gating failed: {exc}', file=sys.stderr)
        sys.exit(1)
