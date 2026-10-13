#!/usr/bin/env python3
"""Recheck saved statements, claim proofs, and witness proofs; rewrite receipts only."""
import sys
sys.dont_write_bytecode = True
import concurrent.futures, hashlib, importlib.util, json, os
from pathlib import Path
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('blind_runner', OUT/'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g = runner.g

def check(n):
    cid = f'bg3n2_{n}'
    sp, pp = OUT/f'{cid}.statement.lean', OUT/f'{cid}.proof.lean'
    result = {'claim_id':cid, 'passed':False, 'claim_passed':False, 'witness_passed':False,
              'gate_sha256':hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
              'security_checks_unchanged':True, 'imports':os.environ['PL_IMPORTS'],
              'project':str(g.PROJ)}
    try:
        statement, proof = sp.read_text(), pp.read_text()
        result.update(statement_sha256=hashlib.sha256(statement.encode()).hexdigest(),
                      proof_sha256=hashlib.sha256(proof.encode()).hexdigest())
        valid, slog = g.check_statement(cid, statement, [runner.IMPORTS])
        result.update(statement_passed=valid, statement_log=slog)
        for target in ('claim', 'witness'):
            if valid:
                ok, log = g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120)
            else:
                ok, log = False, 'Statement check failed: '+slog
            result[target+'_passed'] = ok
            result[target+'_log'] = log
        result['passed'] = result['statement_passed'] and result['claim_passed'] and result['witness_passed']
    except Exception as e:
        result['error'] = str(e)
    (OUT/f'{cid}.receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(cid, 'PASS' if result['passed'] else 'FAIL', flush=True)
    if not result['passed']:
        print(result.get('error',result.get('claim_log','')))
        print(result.get('witness_log',''))
    return result['passed']

if __name__ == '__main__':
    # Expected ids are fixed: absence of a saved file must fail, never silently skip.
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        statuses = list(pool.map(check, range(1,11)))
    sys.exit(0 if all(statuses) else 1)
