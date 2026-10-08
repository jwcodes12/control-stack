"""Verify stored SC-03 receipts against source hashes without promoting assumptions."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
manifest = json.loads((ROOT/'assurance/egress-boundary-v1.json').read_text())
for group in (manifest['implementation'],manifest['evidence'],manifest['theorem']['files']):
    for path,expected in group.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected, 'stale receipt: '+path
full = json.loads((ROOT/'egress/results/local-full.json').read_text())
assert full['status']=='pass' and all(row['status']=='pass' for row in full['results'])
assert full['packet_statistics']['dropped']==0 and not full['gateway_syn_provenance']['orphan_syns']
assert len(full['results'])==manifest['results']['cases']
for path,expected in manifest['implementation'].items():
    assert full['hashes'][Path(path).name]==expected, 'runtime source differs: '+path
expected = json.loads((ROOT/'egress/expected_outcomes.json').read_text())
assert full['expected']==expected
assert {r['id'] for r in full['results']}=={r['id'] for r in expected}|{'startup-inherited-socket','gateway-down','gateway-restart','invalid-policy'}
for mode in ('namespace','packet','mirror'):
    report = json.loads((ROOT/f'egress/results/local-{mode}-mutation.json').read_text())
    assert report['status']=='mutation-detected' and report['packet_statistics']['dropped']==0
    if mode!='namespace':
        assert any('forbidden host packet' in reason for row in report['results'] for reason in row.get('reasons',[]))
assert json.loads((ROOT/'egress/results/local-parser.json').read_text())['status']=='partial-pass'
assert json.loads((ROOT/'egress/results/local-unprivileged.json').read_text())['status']=='blocked'
assert manifest['verdict']=='CONDITIONAL' and any(a['status']=='UNRESOLVED' for a in manifest['assumptions'])
print('SC-03 receipts: source hashes match; 62 full cases and 3 mutations pass; verdict CONDITIONAL')
