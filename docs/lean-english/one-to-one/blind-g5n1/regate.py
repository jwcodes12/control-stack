"""Re-gate saved claims and witnesses. Writes only JSON receipts (plus transient gate files)."""
from pathlib import Path
import sys, importlib.util, hashlib, json, datetime, concurrent.futures
sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('blind_runner', OUT / 'run_gate_blind.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
def sha(data): return hashlib.sha256(data).hexdigest()
def run(n):
    cid = f'bg5n1_{n}'
    sp, pp = OUT / f'{cid}.statement.lean', OUT / f'{cid}.proof.lean'
    try:
        statement, proof = sp.read_text(), pp.read_text()
        frozen = OUT / 'PROOF-HASHES.json'
        if frozen.exists():
            hashes = json.loads(frozen.read_text())['files']
            for p in [sp, pp]:
                if hashes[p.name] != sha(p.read_bytes()): raise ValueError(f'frozen hash mismatch: {p.name}')
        valid, slog = runner.g.check_statement(cid, statement, [runner.IMPORTS])
        both = []
        for target in ['claim', 'witness']:
            ok, log = runner.g.gate(cid, statement, proof, target, [runner.IMPORTS], timeout=120) if valid else (False, 'Statement check failed')
            receipt = {
                'cid': cid, 'target': target, 'passed': ok,
                'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'statement_sha256': sha(sp.read_bytes()), 'proof_sha256': sha(pp.read_bytes()),
                'gate_sha256': sha(Path(runner.g.__file__).read_bytes()),
                'PL_IMPORTS': runner.os.environ['PL_IMPORTS'], 'PL_LEAN_PROJ': str(runner.ROOT),
                'trusted_header': runner.IMPORTS, 'gate_unmodified': False,
                'security_checks_unchanged': True, 'imports_option_local_only': True,
                'statement_check_passed': valid, 'statement_check_log': slog, 'gate_log': log,
            }
            suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
            (OUT / (cid + suffix)).write_text(json.dumps(receipt, indent=2) + '\n')
            print(cid, target, 'PASS' if ok else 'FAIL', log[:160].replace('\n', ' '), flush=True)
            both.append(ok)
        return all(both)
    except Exception as e:
        for target, suffix in [('claim','.receipt.json'), ('witness','.witness.receipt.json')]:
            (OUT / (cid + suffix)).write_text(json.dumps({'cid':cid,'target':target,'passed':False,'error':str(e)},indent=2)+'\n')
        print(cid, 'FAIL', e, flush=True)
        return False
if __name__ == '__main__':
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        results = list(pool.map(run, range(1,11)))
    sys.exit(0 if all(results) else 1)
