"""Recheck frozen statements, Claim proofs, and Witness proofs; write receipts only."""
from pathlib import Path
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


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    all_ok = True
    for n in range(1, 11):
        cid = f'bg4n2_{n}'
        receipt = {'cid': cid, 'passed': False, 'claim_passed': False,
                   'witness_passed': False, 'security_checks_unchanged': True,
                   'gate_sha256': sha(Path(g.__file__).read_bytes()),
                   'PL_IMPORTS': os.environ['PL_IMPORTS'],
                   'PL_LEAN_PROJ': os.environ['PL_LEAN_PROJ']}
        try:
            statement_bytes = (OUT / f'{cid}.statement.lean').read_bytes()
            proof_bytes = (OUT / f'{cid}.proof.lean').read_bytes()
            statement, proof = statement_bytes.decode(), proof_bytes.decode()
            receipt.update(statement_sha256=sha(statement_bytes),
                           proof_sha256=sha(proof_bytes))
            ok, log = g.check_statement(cid, statement, [runner.IMPORTS])
            receipt.update(statement_passed=ok, statement_log=log)
            for target in ('claim', 'witness'):
                passed, log = (g.gate(cid, statement, proof, target,
                                     [runner.IMPORTS], timeout=120)
                               if ok else (False, 'Statement check failed'))
                receipt[target + '_passed'] = passed
                receipt[target + '_log'] = log
            receipt['passed'] = receipt['claim_passed'] and receipt['witness_passed']
        except Exception as exc:
            receipt['error'] = f'{type(exc).__name__}: {exc}'
        (OUT / f'{cid}.receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        all_ok = all_ok and receipt['passed']
        print(cid, 'claim=', receipt['claim_passed'],
              'witness=', receipt['witness_passed'], flush=True)
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main())
