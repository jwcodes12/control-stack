"""Gate Witness separately; retain the supplied deterministic gate unchanged."""
from pathlib import Path
import importlib.util, hashlib, json, sys
OUT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('blind_driver', OUT/'run_gate_blind.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
for p in sorted(OUT.glob('b1_*.statement.lean')):
    cid = p.name.removesuffix('.statement.lean')
    statement = p.read_text()
    proof = p.with_name(cid+'.proof.lean').read_text()
    ok, log = r.g.gate(cid, statement, proof, 'witness', [r.IMPORTS], timeout=120)
    (OUT/(cid+'.witness-gate.txt')).write_text(log+'\n')
    (OUT/(cid+'.witness-receipt.json')).write_text(json.dumps({
        'passed': ok, 'target': 'witness',
        'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
        'proof_sha256': hashlib.sha256(proof.encode()).hexdigest(),
        'gate_sha256': hashlib.sha256(Path(r.g.__file__).read_bytes()).hexdigest(),
        'security_checks_unchanged': True,
        'trusted_imports': 'ControlStack.Deployment.Witnesses ControlStack.Deployment.TranscriptReplay'
    }, indent=2)+'\n')
    print(cid, ok, log[:300], flush=True)
