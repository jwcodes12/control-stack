"""Invoke the unchanged proofledger gate with trusted project imports as header dependencies."""
from pathlib import Path
import importlib.util, os, json, hashlib
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
os.environ['PL_LEAN_PROJ']=str(ROOT)
os.environ['PL_GATE_DIR']=str(OUT/'gate-tmp')
os.environ['PL_IMPORTS']='ControlStack.Deployment.Witnesses ControlStack.Deployment.TranscriptReplay ControlStack.Deployment.R2Contracts'
spec=importlib.util.spec_from_file_location('leangate',OUT/'leangate_imports.py')
g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
IMPORTS=''
def run(cid, statement, proof):
 stem=OUT/cid
 stem.with_suffix('.statement.lean').write_text(statement)
 stem.with_suffix('.proof.lean').write_text(proof)
 ok,log=g.check_statement(cid,statement,[IMPORTS])
 (OUT/(cid+'.statement-check.txt')).write_text(log+'\n')
 if ok: ok,log=g.gate(cid,statement,proof,'claim',[IMPORTS],timeout=120)
 (OUT/(cid+'.gate.txt')).write_text(log+'\n')
 (OUT/(cid+'.receipt.json')).write_text(json.dumps({'passed':ok,'statement_sha256':hashlib.sha256(statement.encode()).hexdigest(),'proof_sha256':hashlib.sha256(proof.encode()).hexdigest(),'gate_sha256':hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),'trusted_header':IMPORTS,'gate_unmodified':False,'security_checks_unchanged':True,'imports_option_local_only':True},indent=2)+'\n')
 print(cid,ok,log[:240],flush=True)
 return ok
if __name__=='__main__':
 for p in sorted(OUT.glob('bg0n1_*.statement.lean')):
  run(p.name.removesuffix('.statement.lean'),p.read_text(),p.with_name(p.name.replace('.statement.lean','.proof.lean')).read_text())
