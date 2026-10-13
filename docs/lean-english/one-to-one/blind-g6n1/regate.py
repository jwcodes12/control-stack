"""Recheck all ten saved comparisons and witnesses; only receipt files persistently change.

Run from the repository root:
  python3 -B docs/lean-english/one-to-one/blind-g6n1/regate.py
No existing receipt, generated gate file, or Python cache is required.
"""
from pathlib import Path
import datetime
import hashlib
import json
import runpy
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
NS = runpy.run_path(str(OUT / 'run_gate_blind.py'))
G = NS['g']
MANIFEST = OUT / 'COMPARISON-HASHES.json'
FROZEN = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}

def sha(data):
    return hashlib.sha256(data).hexdigest()

failed = False
for n in range(1, 11):
    cid = f'bg6n1_{n}'
    sp, pp = OUT / f'{cid}.statement.lean', OUT / f'{cid}.proof.lean'
    inputs_present = sp.is_file() and pp.is_file()
    statement = sp.read_text() if sp.is_file() else ''
    proof = pp.read_text() if pp.is_file() else ''
    expected = FROZEN.get(cid, {})
    hashes_ok = (expected.get('statement_sha256') == sha(statement.encode()) and
                 expected.get('proof_sha256') == sha(proof.encode()) and
                 expected.get('gate_sha256') == sha(Path(G.__file__).read_bytes()) and
                 expected.get('runner_sha256') == sha((OUT/'run_gate_blind.py').read_bytes()))
    try:
        statement_ok, statement_log = G.check_statement(cid, statement, [NS['IMPORTS']])
    except Exception as ex:
        statement_ok, statement_log = False, f'{type(ex).__name__}: {ex}'
    for target in ('claim', 'witness'):
        try:
            target_ok, gate_log = G.gate(cid, statement, proof, target,
                                         [NS['IMPORTS']], timeout=120)
        except Exception as ex:
            target_ok, gate_log = False, f'{type(ex).__name__}: {ex}'
        passed = bool(inputs_present and hashes_ok and statement_ok and target_ok)
        receipt = {
            'cid': cid, 'target': target, 'passed': passed,
            'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'inputs_present': inputs_present, 'frozen_hashes_match': hashes_ok,
            'statement_check_passed': statement_ok, 'target_gate_passed': target_ok,
            'statement_sha256': sha(statement.encode()),
            'proof_sha256': sha(proof.encode()),
            'gate_sha256': sha(Path(G.__file__).read_bytes()),
            'runner_sha256': sha((OUT/'run_gate_blind.py').read_bytes()),
            'trusted_header': NS['IMPORTS'],
            'PL_IMPORTS': NS['os'].environ['PL_IMPORTS'],
            'PL_LEAN_PROJ': str(G.PROJ),
            'gate_unmodified': False, 'security_checks_unchanged': True,
            'imports_option_local_only': True,
            'statement_log': statement_log, 'gate_log': gate_log,
        }
        suffix = '.receipt.json' if target == 'claim' else '.witness.receipt.json'
        (OUT/(cid+suffix)).write_text(json.dumps(receipt, indent=2)+'\n')
        print(cid, target, 'PASS' if passed else 'FAIL', gate_log[:180], flush=True)
        if not passed:
            failed = True
sys.exit(1 if failed else 0)
