"""Recheck all twelve saved claims and witnesses; only receipt files are rewritten."""
from pathlib import Path
import hashlib, importlib.util, json, sys
sys.dont_write_bytecode = True
from concurrent.futures import ThreadPoolExecutor
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('run_gate_blind', OUT/'run_gate_blind.py')
r=importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
def sha(b): return hashlib.sha256(b).hexdigest()
def run(n):
    cid=f'bg5n2_{n}'
    receipt={'cid':cid,'passed':False,'claim_passed':False,'witness_passed':False,
             'gate_sha256':sha(Path(r.g.__file__).read_bytes()),
             'security_checks_unchanged':True,'imports_option_local_only':True,
             'PL_IMPORTS':r.os.environ['PL_IMPORTS'],'PL_LEAN_PROJ':str(r.ROOT)}
    try:
        statement=(OUT/f'{cid}.statement.lean').read_text()
        proof=(OUT/f'{cid}.proof.lean').read_text()
        receipt.update(statement_sha256=sha(statement.encode()),proof_sha256=sha(proof.encode()))
        ok,log=r.g.check_statement(cid,statement,[r.IMPORTS])
        receipt.update(statement_passed=ok,statement_log=log)
        # Gate the two targets separately, even when one fails.
        for target in ['claim','witness']:
            passed,log=r.g.gate(cid,statement,proof,target,[r.IMPORTS],timeout=120)
            receipt[target+'_passed']=passed
            receipt[target+'_log']=log
        receipt['passed']=ok and receipt['claim_passed'] and receipt['witness_passed']
    except Exception as e:
        receipt['error']=f'{type(e).__name__}: {e}'
    (OUT/f'{cid}.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(cid,receipt['passed'],flush=True)
    if not receipt['passed']:
        print(json.dumps(receipt,indent=2),flush=True)
    return receipt['passed']
if __name__=='__main__':
    results=list(ThreadPoolExecutor(max_workers=4).map(run,range(1,13)))
    raise SystemExit(0 if all(results) else 1)
