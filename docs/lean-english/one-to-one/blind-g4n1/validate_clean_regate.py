"""Validate re-gating with no receipts or scratch state, preserving all saved Lean inputs."""
from pathlib import Path
import subprocess,hashlib,json,shutil,datetime
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[3]
inputs=list(OUT.glob('bg4n1_*.statement.lean'))+list(OUT.glob('bg4n1_*.proof.lean'))+list(OUT.glob('bg4n1_*.witness.lean'))+list((OUT/'typed').glob('*'))
def hashes():
    return {str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs if p.is_file()}
before=hashes()
for p in OUT.glob('bg4n1_*.receipt.json'): p.unlink()
for sub in ['gate-tmp','__pycache__']:
    if (OUT/sub).exists(): shutil.rmtree(OUT/sub)
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (OUT/'regate-clean.log').open('w') as log:
    r=subprocess.run(['python3',str(OUT/'regate.py')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=900)
receipts={p.name:json.loads(p.read_text())['passed'] for p in OUT.glob('bg4n1_*.receipt.json')}
after=hashes()
passed=r.returncode==0 and len(receipts)==20 and all(receipts.values()) and before==after
result={'passed':passed,'started_at_utc':started,'completed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':r.returncode,'receipts_removed_before_run':True,'scratch_and_python_cache_removed_before_run':True,'receipt_count':len(receipts),'all_receipts_passed':all(receipts.values()),'saved_inputs_byte_identical':before==after,'saved_input_sha256':after,'receipts':receipts}
(OUT/'regate-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['saved_input_sha256','receipts']},indent=2),flush=True)
raise SystemExit(0 if passed else 1)
