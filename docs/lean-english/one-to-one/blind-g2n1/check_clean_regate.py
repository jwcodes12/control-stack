"""Exercise regate with no existing receipts or gate temporary directory."""
from pathlib import Path
import datetime, hashlib, json, shutil, subprocess
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[3]
receipt_names={f'bg2n1_{n}{suffix}' for n in range(1,11)
               for suffix in ('.receipt.json','.witness.receipt.json')}
archive=OUT/'attempts/before-clean'
archive.mkdir(parents=True,exist_ok=True)
for name in receipt_names:
    p=OUT/name
    if p.exists():
        shutil.copyfile(p,archive/name)
        p.unlink()
shutil.rmtree(OUT/'gate-tmp',ignore_errors=True)

def snapshot():
    return {str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in OUT.rglob('*') if p.is_file()}

before=snapshot()
assert not any(name in before for name in receipt_names)
start=datetime.datetime.now(datetime.timezone.utc)
r=subprocess.run(['python3',str(OUT/'regate.py')],cwd=ROOT,capture_output=True,text=True)
after=snapshot()
changed={p for p in set(before)|set(after) if before.get(p)!=after.get(p)}
only_receipts=changed==receipt_names
all_passed=all((OUT/n).exists() and json.loads((OUT/n).read_text()).get('passed') is True
               for n in receipt_names)
result={'started_utc':start.isoformat(),'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'exit_code':r.returncode,'started_without_receipts':True,'started_without_gate_tmp':True,
        'persistent_changes_only_receipts':only_receipts,'all_20_targets_passed':all_passed,
        'changed_files':sorted(changed),'regate_stdout':r.stdout,'regate_stderr':r.stderr,
        'nonreceipt_files_before_sha256':before,
        'initial_failure_exit_code_observed':1}
(OUT/'clean-regate-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(r.stdout, end='')
print(r.stderr, end='')
assert r.returncode==0 and only_receipts and all_passed, result
print('CLEAN REGATE PASSED: only the twenty receipts were persistently written.')
