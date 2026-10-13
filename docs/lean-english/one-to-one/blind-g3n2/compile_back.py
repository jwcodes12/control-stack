from pathlib import Path
import concurrent.futures, hashlib, json, subprocess
from datetime import datetime, timezone
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
source_hashes = json.loads((OUT/'back/BACK-HASHES.json').read_text())['files']
for rel, digest in source_hashes.items():
    assert hashlib.sha256((OUT/rel).read_bytes()).hexdigest() == digest, rel
for sub in ('typed', 'compile-fixes', 'compile-logs'):
    (OUT/sub).mkdir(exist_ok=True)
def compile_one(p):
    n = p.name.split('-')[0]
    result = subprocess.run(['lake', 'env', 'lean', str(p)], cwd=ROOT, capture_output=True, text=True, timeout=180)
    (OUT/'compile-logs'/f'{n}.as-written.txt').write_text(f'exit_code={result.returncode}\n'+result.stdout+result.stderr)
    print(n, result.returncode, result.stdout+result.stderr, flush=True)
    if result.returncode == 0:
        (OUT/'typed'/p.name).write_bytes(p.read_bytes())
        (OUT/'compile-fixes'/f'{n}.diff').write_text('No repair: compiled as written. Meaning unchanged.\n')
    return {'claim': int(n), 'exit_code': result.returncode}
files = sorted((OUT/'back').glob('*.lean'), key=lambda p:int(p.name.split('-')[0]))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    results = list(pool.map(compile_one, files))
(OUT/'compile-logs/SUMMARY.json').write_text(json.dumps(results, indent=2)+'\n')
assert all(r['exit_code']==0 for r in results), 'Repair needed; do not read originals yet'
hashes = {f'typed/{p.name}':hashlib.sha256((OUT/'typed'/p.name).read_bytes()).hexdigest() for p in files}
(OUT/'typed/HASHES.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(), 'original_declarations_opened':False, 'files':hashes},indent=2)+'\n')
print('All typed hashes frozen BEFORE opening originals.', flush=True)
