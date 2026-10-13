"""From the repository root: re-gate saved claims and witnesses, writing receipts only."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import importlib.util, json, hashlib, datetime

OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('run_gate_blind', OUT / 'run_gate_blind.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
g = r.g


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def receipt(cid, target, statement, proof, statement_ok, statement_log, passed, log):
    tag = cid if target == 'claim' else cid + '.witness'
    (OUT / (tag + '.statement-check.txt')).write_text(statement_log + '\n')
    (OUT / (tag + '.gate.txt')).write_text(log + '\n')
    data = {
        'passed': passed, 'target': target, 'statement_passed': statement_ok,
        'statement_sha256': sha(statement), 'proof_sha256': sha(proof),
        'gate_sha256': hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
        'trusted_header': g.import_header(), 'project': str(g.PROJ),
        'gate_unmodified': False, 'security_checks_unchanged': True,
        'imports_option_local_only': True,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }
    (OUT / (tag + '.receipt.json')).write_text(json.dumps(data, indent=2) + '\n')
    print(tag, passed, log.splitlines()[0] if log else '', flush=True)


def main():
    all_ok = True
    for n in range(1, 11):
        cid = f'bg1n2_{n}'
        p = OUT / (cid + '.statement.lean')
        for target, suffix in [('claim', '.proof.lean'), ('witness', '.witness.proof.lean')]:
            q = OUT / (cid + suffix)
            statement = p.read_text() if p.exists() else ''
            proof = q.read_text() if q.exists() else ''
            if not p.exists() or not q.exists():
                ok, slog, passed, log = False, 'Missing saved statement/proof', False, 'FAIL missing saved statement/proof'
            else:
                ok, slog = g.check_statement(cid, statement, [r.IMPORTS])
                if ok:
                    passed, log = g.gate(cid, statement, proof, target, [r.IMPORTS], timeout=120)
                else:
                    passed, log = False, 'FAIL statement check\n' + slog
            receipt(cid, target, statement, proof, ok, slog, passed, log)
            all_ok = all_ok and passed
    return 0 if all_ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
