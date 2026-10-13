"""Re-gate saved comparisons and witnesses; write only receipts (plus removed gate scratch files)."""
from pathlib import Path
import sys,importlib.util,json,hashlib,os
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('blind_gate_runner',OUT/'run_gate_blind.py')
runner=importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
g=runner.g

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def main():
    failed=False
    for n in range(1,11):
        cid=f'bg4n1_{n}'
        sp=OUT/f'{cid}.statement.lean'
        try:
            statement=sp.read_text()
            stmt_ok,stmt_log=g.check_statement(cid,statement,[runner.IMPORTS])
        except Exception as e:
            statement=''
            stmt_ok,stmt_log=False,f'{type(e).__name__}: {e}'
        for target,suffix in [('claim','proof'),('witness','witness')]:
            pp=OUT/f'{cid}.{suffix}.lean'
            try:
                proof=pp.read_text()
                if stmt_ok:
                    ok,log=g.gate(cid,statement,proof,target,[runner.IMPORTS],timeout=120)
                else:
                    ok,log=False,'Statement check failed: '+stmt_log
            except Exception as e:
                proof=''
                ok,log=False,f'{type(e).__name__}: {e}'
            receipt={
                'cid':cid,'target':target,'passed':ok,'statement_check_passed':stmt_ok,
                'statement_sha256':sha(statement),'proof_sha256':sha(proof),
                'gate_sha256':hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
                'trusted_header':runner.IMPORTS,'project':str(g.PROJ),
                'PL_IMPORTS':os.environ['PL_IMPORTS'],
                'gate_unmodified':False,'security_checks_unchanged':True,
                'imports_option_local_only':True,
                'statement_log':stmt_log,'gate_log':log,
            }
            rp=OUT/(cid+('.receipt.json' if target=='claim' else '.witness.receipt.json'))
            rp.write_text(json.dumps(receipt,indent=2)+'\n')
            print(cid,target,'PASS' if ok else 'FAIL',log[:500],flush=True)
            failed=failed or not ok
    return 1 if failed else 0

if __name__=='__main__':
    raise SystemExit(main())
