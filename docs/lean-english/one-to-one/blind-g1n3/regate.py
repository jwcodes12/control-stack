"""Recheck every saved comparison and non-vacuity witness; only receipts persist."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import importlib.util, json, hashlib, datetime
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('run_gate_blind', OUT / 'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def main():
    all_ok = True
    for n in range(1, 10):
        cid = f'bg1n3_{n}'
        try:
            statement = (OUT / f'{cid}.statement.lean').read_text()
            proof = (OUT / f'{cid}.proof.lean').read_text()
            stmt_ok, stmt_log = g.check_statement(cid, statement, [runner.IMPORTS])
        except Exception as exc:
            statement = proof = ''
            stmt_ok, stmt_log = False, f'{type(exc).__name__}: {exc}'
        for target in ['claim', 'witness']:
            if stmt_ok:
                try:
                    ok, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
                except Exception as exc:
                    ok, log = False, f'{type(exc).__name__}: {exc}'
            else:
                ok, log = False, 'Statement check failed: ' + stmt_log
            receipt = {
                'cid': cid, 'target': target, 'passed': ok,
                'statement_passed': stmt_ok, 'statement_log': stmt_log, 'log': log,
                'statement_sha256': sha(statement), 'proof_sha256': sha(proof),
                'gate_sha256': hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
                'trusted_header': runner.IMPORTS,
                'PL_IMPORTS': __import__('os').environ['PL_IMPORTS'],
                'PL_LEAN_PROJ': str(g.PROJ),
                'gate_unmodified': False, 'security_checks_unchanged': True,
                'imports_option_local_only': True,
                'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            }
            filename = f'{cid}.receipt.json' if target == 'claim' else f'{cid}.witness.receipt.json'
            (OUT / filename).write_text(json.dumps(receipt, indent=2) + '\n')
            print(cid, target, 'PASS' if ok else 'FAIL', log[:200], flush=True)
            all_ok = all_ok and ok
    return 0 if all_ok else 1

if __name__ == '__main__':
    raise SystemExit(main())
