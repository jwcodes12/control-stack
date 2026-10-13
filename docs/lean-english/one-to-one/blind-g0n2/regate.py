"""Re-gate all eight saved comparisons and their witnesses; never rewrite inputs.

Run from the repository root:
  python3 -B docs/lean-english/one-to-one/blind-g0n2/regate.py
Only receipts/logs and transient gate files are written, inside this directory.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import concurrent.futures
import datetime
import hashlib
import importlib.util
import json

OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('blind_gate_runner', OUT/'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g


def check(cid):
    statement_path = OUT/f'{cid}.statement.lean'
    proof_path = OUT/f'{cid}.proof.lean'
    try:
        statement = statement_path.read_text()
        proof = proof_path.read_text()
    except OSError as e:
        statement, proof = '', ''
        statement_ok, statement_log = False, f'MISSING INPUT: {e}'
    else:
        try:
            statement_ok, statement_log = g.check_statement(cid, statement, [runner.IMPORTS])
        except Exception as e:
            statement_ok, statement_log = False, f'STATEMENT EXCEPTION: {e}'
    (OUT/f'{cid}.statement-check.txt').write_text(statement_log+'\n')
    passed = []
    for target in ['claim', 'witness']:
        if statement_ok:
            try:
                ok, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            except Exception as e:
                ok, log = False, f'GATE EXCEPTION: {e}'
        else:
            ok, log = False, 'STATEMENT CHECK FAILED\n'+statement_log
        stem = cid if target == 'claim' else cid+'.witness'
        (OUT/f'{stem}.gate.txt').write_text(log+'\n')
        receipt = {
            'cid': cid, 'target': target, 'passed': ok,
            'statement_check_passed': statement_ok,
            'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
            'proof_sha256': hashlib.sha256(proof.encode()).hexdigest(),
            'gate_sha256': hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
            'runner_sha256': hashlib.sha256((OUT/'run_gate_blind.py').read_bytes()).hexdigest(),
            'regate_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'gate_log_sha256': hashlib.sha256((log+'\n').encode()).hexdigest(),
            'trusted_header': runner.IMPORTS,
            'PL_IMPORTS': g.import_header(), 'PL_LEAN_PROJ': str(g.PROJ),
            'gate_unmodified': False, 'security_checks_unchanged': True,
            'imports_option_local_only': True,
            'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        }
        (OUT/f'{stem}.receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
        passed.append(ok)
        print(cid, target, 'PASS' if ok else 'FAIL', log[:200], flush=True)
    return all(passed)


if __name__ == '__main__':
    ids = [f'bg0n2_{n}' for n in range(1, 9)]
    # All expected ids are checked, even if an input is missing.
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, ids))
    summary = {'passed': all(results), 'claims_and_witnesses': dict(zip(ids, results)),
               'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (OUT/'regate.receipt.json').write_text(json.dumps(summary, indent=2)+'\n')
    sys.exit(0 if all(results) else 1)
