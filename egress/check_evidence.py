"""Verify stored SC-03 receipts against source hashes without promoting assumptions."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
manifest = json.loads((ROOT/'assurance/egress-boundary-v1.json').read_text())
for group in (manifest['implementation'],manifest['evidence'],manifest['theorem']['files'],manifest.get('experimental',{}).get('files',{})):
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
outer = json.loads((ROOT/'egress/results/local-outer-accounting.json').read_text())
assert outer['status']=='pass' and outer['netns']!=outer['host_netns']
assert outer['packet_statistics']['dropped']==0 and not outer['errors']
assert len(outer['flows'])==8 and len({f['pid'] for f in outer['flows']})==2
assert outer['missing_trace_mutation_detected']
for path,expected_hash in outer['hashes'].items():
    assert hashlib.sha256((ROOT/'egress'/path).read_bytes()).hexdigest()==expected_hash
keys = ('src','source_port','dst','port','protocol')
flow_key = lambda r: tuple(r[k] for k in keys)
assert {flow_key(f) for f in outer['flows']}=={flow_key(p) for p in outer['attributed_initial_packets']}
for packet in outer['attributed_initial_packets']:
    pids = {f['pid'] for f in outer['flows'] if flow_key(f)==flow_key(packet) and f['t']<=packet['t']}
    assert len(pids)==1 and sorted(pids)==packet['pids']
assert next(a for a in manifest['assumptions'] if a['id']=='all_destination_attribution')['status']=='UNRESOLVED'
print('SC-03 receipts: hashes match; 62 full cases, 3 mutations, isolated 8-flow calibration pass; verdict CONDITIONAL')
