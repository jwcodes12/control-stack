#!/usr/bin/env python3
"""Independent byte/daemon-inventory checks of the archived real-container run.
This does not authenticate Docker or prove universal protocol refinement.
"""
import argparse
import base64
import hashlib
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from extractors.compose import collect,sha
from tools.collect_deployment_docker import normalize
from security_ir.verifier import verify

def check(output):
    output=Path(output).resolve();pin=json.loads((ROOT/'deployment/legacy-image-pin.json').read_text())
    for path,digest in pin['source_sha256'].items():assert sha(ROOT/path)==digest,('image source drift',path)
    assert sha(ROOT/'deployment/legacy-container-entry.py')==pin['entry_sha256']
    result=json.loads((output/'result.json').read_text())
    assert result['image']==pin['image']
    assert set(result['cases'])=={'clean','writable-sink-mount','trusted-role-uid-collision'}
    info=json.loads((output/'docker-info.json').read_text())
    assert not any('rootless' in x or 'userns' in x for x in info['SecurityOptions']), 'UID remap outside experiment scope'
    for case,expected in result['cases'].items():
        dest=output/case
        original=dest/'compose.json'
        assert all(s['image']==pin['image'] for s in json.loads(original.read_text())['services'].values()),('archived image pin differs',case)
        c=json.loads(original.read_text());r=json.loads((dest/'runtime.json').read_text())
        raw=(dest/'docker-inspect.raw.json').read_bytes()
        assert hashlib.sha256(raw).hexdigest()==r['capture']['raw_sha256']
        rows=json.loads(raw)
        assert len(rows)==6 and all(row['State']['Running'] for row in rows)
        assert r['services']==normalize(c,rows,'sol-pr45-followup'),('normalized daemon facts differ',case)
        assert all('unsupported_runtime_security' not in f for f in r['services'].values())
        ir=collect(original,dest/'runtime.json',sha(original))
        stored_ir=json.loads((dest/'ir.json').read_text())
        def portable(d):
            d=json.loads(json.dumps(d))
            for p in d['sources']+[n['provenance'] for n in d['nodes']+d['edges']]:
                if p['sha256']==sha(dest/'runtime.json'):p['source']='runtime.json'
                elif p['sha256']==sha(original):p['source']='compose.json'
                for root in (str(ROOT),str(Path(pin['host_root']).parent)):
                    if p['source'].startswith(root+'/'):p['source']=p['source'][len(root)+1:]
            return d
        assert portable(ir)==portable(stored_ir),('IR mismatch',case)
        bundle=json.loads((dest/'bundle.json').read_text())
        assert bundle['ir_sha256']==verify(stored_ir)['ir_sha256']
        marker=dest/'sink/.gitkeep'
        if marker.exists():assert marker.read_bytes()==b'', 'invalid empty-directory archival marker'
        actual={p.name:{'sha256':sha(p),'body_b64':base64.b64encode(p.read_bytes()).decode(),'size':p.stat().st_size} for p in sorted((dest/'sink').iterdir()) if p.is_file() and p.name!='.gitkeep'}
        assert actual==json.loads((dest/'sink-state.json').read_text())==expected['sink_files']
        assert bundle['verdict']==expected['verdict']
        if case=='clean':
            assert list(actual)==['1.body'] and base64.b64decode(actual['1.body']['body_b64'])==b'exact-reviewed-two-agent-container-slice'
        elif case=='writable-sink-mount':
            assert list(actual)==['2.body'] and base64.b64decode(actual['2.body']['body_b64'])==b'unapproved real container mount'
        else:assert actual=={}
    print('PASS: same pinned Compose, raw Docker-derived inventory and actual sink bytes; daemon/refinement remain conditional')
    return True
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('output');a=ap.parse_args();check(a.output)
