from pathlib import Path
import os,json,hashlib,datetime,concurrent.futures,argparse
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
# Preserve the copied runner's unchanged ROOT expression by supplying its original
# location as __file__. Executed code comes exclusively from run_gate_blind.py.
ctx={'__file__':str(BASE/'run_gate.py'),'__name__':'blind_runner'}
exec(compile((OUT/'run_gate_blind.py').read_text(),str(OUT/'run_gate_blind.py'),'exec'),ctx)
g=ctx['g']
assert g.PROJ == OUT.parents[3], (g.PROJ,OUT.parents[3])
assert (OUT/'leangate_imports.py').read_bytes()==(BASE/'leangate_imports.py').read_bytes()
parser=argparse.ArgumentParser();parser.add_argument('ids',nargs='*');args=parser.parse_args()
paths=sorted(OUT.glob('bg1a_*.statement.lean'))
if args.ids: paths=[p for p in paths if p.name.split('.')[0] in args.ids]
def process(p):
 cid=p.name.removesuffix('.statement.lean')
 statement=p.read_text();proof=p.with_name(cid+'.proof.lean').read_text()
 frozen={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'statement_sha256':hashlib.sha256(statement.encode()).hexdigest(),'proof_sha256':hashlib.sha256(proof.encode()).hexdigest()}
 (OUT/(cid+'.frozen.json')).write_text(json.dumps(frozen,indent=2)+'\n')
 passed=ctx['run'](cid,statement,proof)
 wok,wlog=g.gate(cid,statement,proof,'witness',[ctx['IMPORTS']],timeout=120)
 (OUT/(cid+'.witness-gate.txt')).write_text(wlog+'\n')
 receipt=json.loads((OUT/(cid+'.receipt.json')).read_text())
 receipt.update({'claim_passed':passed,'witness_passed':wok,'PL_IMPORTS':os.environ['PL_IMPORTS'],'PL_LEAN_PROJ':os.environ['PL_LEAN_PROJ'],'gate_byte_identical_to_helper':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 (OUT/(cid+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 (OUT/(cid+'.witness-receipt.json')).write_text(json.dumps({**frozen,'passed':wok,'target':'witness','gate_sha256':receipt['gate_sha256'],'PL_IMPORTS':receipt['PL_IMPORTS']},indent=2)+'\n')
 print(cid,'claim',passed,'witness',wok,wlog[:240],flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 list(pool.map(process,paths))
