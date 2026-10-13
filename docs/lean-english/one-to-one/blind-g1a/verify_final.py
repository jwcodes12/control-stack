from pathlib import Path
import hashlib,json,datetime
out=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
back=json.loads((out/'back/BACK-HASHES.json').read_text())['files']
typed=json.loads((out/'typed/HASHES.json').read_text())
compile_status=json.loads((out/'compile-logs/STATUS.json').read_text())
helper=sha(out/'leangate_imports.py')
assert helper==sha(out.parent/'leangate_imports.py')
src=(out.parent/'run_gate.py').read_text().splitlines();copy=(out/'run_gate_blind.py').read_text().splitlines()
assert len(src)==len(copy)
changed=[a for a,b in zip(src,copy) if a!=b]
assert len(changed)==3 and changed[0].startswith('OUT=') and "PL_IMPORTS" in changed[1] and 'OUT.glob' in changed[2]
rows=[]
for n in range(1,10):
 p=next((out/'typed').glob(f'{n}-*.lean'))
 assert sha(p)==typed['files'][p.name]==back['back/'+p.name]==sha(out/'back'/p.name)
 assert compile_status[p.name]['exit_code']==0
 r=json.loads((out/f'bg1a_{n}.receipt.json').read_text())
 w=json.loads((out/f'bg1a_{n}.witness-receipt.json').read_text())
 f=json.loads((out/f'bg1a_{n}.frozen.json').read_text())
 assert r['passed'] and r['claim_passed'] and r['witness_passed'] and w['passed']
 assert r['gate_sha256']==w['gate_sha256']==helper
 for ext,key in [('statement.lean','statement_sha256'),('proof.lean','proof_sha256')]:
  assert sha(out/f'bg1a_{n}.{ext}')==r[key]==w[key]==f[key]
 assert 'PASS claim axioms=' in (out/f'bg1a_{n}.gate.txt').read_text()
 assert 'PASS witness axioms=' in (out/f'bg1a_{n}.witness-gate.txt').read_text()
 rows.append({'claim':n,'verdict':'EQUIVALENT','claim_gate_passed':True,'witness_gate_passed':True,'current_hashes_match_receipts':True})
root=out.parents[3]
for record in json.loads((out/'ORIGINAL-SIGNATURES.json').read_text())['declarations']:
 assert sha(root/record['path'])==record['sha256']
now=datetime.datetime.now(datetime.timezone.utc)
validation={'utc':now.isoformat(),'claims':rows,'back_and_typed_hashes_intact':True,'gate_helper_unchanged':True,'runner_only_three_permitted_edits':True,'original_modules_unchanged_since_inspection':True}
(out/'FINAL-VALIDATION.json').write_text(json.dumps(validation,indent=2)+'\n')
(out/'PROGRESS.md').write_text(f'''# Blind G1a Phase B progress

Status: DONE — 9/9 claims, 9/9 comparison gates, 9/9 separately targeted Witness gates.

Started approximately 2026-10-13 03:52 UTC. Finished {now.strftime('%Y-%m-%d %H:%M:%S UTC')} (approximately {(now-datetime.datetime(2026,10,13,3,52,tzinfo=datetime.timezone.utc)).total_seconds()/60:.1f} minutes).
Typed copies frozen before opening originals: {typed['utc']}.

Done:
- Checked all nine Phase-A hashes and compiled every back file as written.
- Wrote byte-identical typed copies, SHA-256 manifest and nine no-repair records before reading original declarations.
- Inspected the nine original signatures and relevant model definitions.
- Proved pointwise comparisons, including the probabilistic-to-deterministic strategy extraction for claim 3.
- Passed the unchanged deterministic gate for all comparisons and separately for all Witness targets.
- Audited every “Does NOT say” item and wrote replacement sentences and ambiguities in RESULTS.md.
- Preserved failed gate attempts, current gate logs, hashes and receipts.
- Checked all current artifacts against their receipts; checked original module hashes remain unchanged since inspection.

Not done: none of the requested nine comparisons, witnesses or report outputs remains unfinished. No claim is UNDECIDED.

What this run could not establish: real sandbox isolation, credential separation, semantic harmlessness, output independence in a deployment, exact installed rules, kernel/runtime correspondence, host test results, or empirical scope of named world assumptions. These are outside the supplied theorem statements and the authorized reading scope; no excluded English documentation or deployment evidence was read.

Operational limits: the umbrella Mathlib module was not built, so PL_IMPORTS uses the already-built Mathlib.Tactic. No build/download was needed. No back repair, gate-security modification, ControlStack edit, git command, or external publication occurred.

Reproduce: `python3 docs/lean-english/one-to-one/blind-g1a/gate_all.py` from the repository root; then run `python3 docs/lean-english/one-to-one/blind-g1a/verify_final.py` to check current receipts and hashes. The copied runner's original ROOT expression is retained through the driver, as explained in RESULTS.md.
''')
print(json.dumps(validation,indent=2))
