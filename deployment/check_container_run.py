#!/usr/bin/env python3
"""Independently read raw daemon inventory, SQLite backups and archived sink bytes."""
import argparse
import base64
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.reconcile import reconcile
from tools.collect_deployment_docker import normalize
from extractors.compose import collect,sha
from security_ir.verifier import verify

def check(output):
    output=Path(output).resolve();pin=json.loads((output/'image-pin.json').read_text());result=json.loads((output/'result.json').read_text())
    assert pin['image']==result['image'] and pin['tag'].startswith('cstack-r2-')
    assert sha(output/'container-entry.py')==pin['entry_sha256']
    for source,digest in pin['source_sha256'].items():assert sha(ROOT/source)==digest,('trusted source drift',source)
    assert set(result['cases'])=={'clean','writable-sink-mount','trusted-role-uid-collision','concurrent-cap1','crash-retry','halt-inflight','drift-uid'}
    for case,expected in result['cases'].items():
        dest=output/case;c=json.loads((dest/'compose.json').read_text())
        assert expected==json.loads((dest/'result.json').read_text())
        assert c['x-cstack']['budget']==expected['final']['global_cap']
        project='cstack-r2-'+case
        for scan_dir in [dest]+([dest/'drift'] if case=='drift-uid' else [])+([dest/'post-restart'] if (dest/'post-restart').exists() else []):
            r=json.loads((scan_dir/'runtime.json').read_text());raw=scan_dir/'docker-inspect.raw.json';rows=json.loads(raw.read_text())
            assert r['capture']['raw_sha256']==sha(raw) and r['capture']['independent_attestation'] is False
            assert len(rows)==6 and all(row['State']['Running'] for row in rows)
            assert r['services']==normalize(c,rows,project)
            ir=collect(dest/'compose.json',scan_dir/'runtime.json',sha(dest/'compose.json'));stored=json.loads((scan_dir/'ir.json').read_text())
            def portable(d):
                d=json.loads(json.dumps(d))
                for p in d['sources']+[x['provenance'] for x in d['nodes']+d['edges']]:
                    if p['sha256']==sha(dest/'compose.json'):p['source']='compose.json'
                    elif p['sha256']==sha(scan_dir/'runtime.json'):p['source']='runtime.json'
                    for root in [str(ROOT),str(Path(pin['host_root']).parent)]:
                        if p['source'].startswith(root+'/'):p['source']=p['source'][len(root)+1:]
                return d
            assert portable(ir)==portable(stored),(case,'IR differs')
            bundle=json.loads((scan_dir/'bundle.json').read_text());assert bundle['ir_sha256']==verify(stored)['ir_sha256']
            assert bundle['lean']['accepted']==(bundle['verdict']=='CONDITIONAL')
            assert 'sorryAx' not in bundle['lean']['axioms']
        bundle=json.loads((dest/'bundle.json').read_text());assert bundle['verdict']==expected['prediction']
        for phase in sorted(p for p in dest.iterdir() if p.is_dir() and (p/'reconciliation.json').exists()):
            marker=phase/'sink/.gitkeep'
            if marker.exists():assert marker.read_bytes()==b''
            assert all(p.is_file() and not p.is_symlink() for p in (phase/'sink').iterdir())
            files={p.name:{'sha256':sha(p),'body_b64':base64.b64encode(p.read_bytes()).decode(),'size':p.stat().st_size} for p in sorted((phase/'sink').iterdir()) if p.is_file() and p.name!='.gitkeep'}
            assert files==json.loads((phase/'sink-state.json').read_text()),(case,phase.name,'sink bytes')
            actual=reconcile(phase/'database.sqlite',phase/'sink');assert actual==json.loads((phase/'reconciliation.json').read_text()),(case,phase.name,'DB/sink state')
            assert all(x['classification']!='inconsistent' for x in actual['records'])
            if phase.name=='final':assert files==expected['sink_files'] and actual==expected['final']
        final=expected['final'];outcomes=expected['outcomes']
        if case=='clean':assert final['admitted']==final['delivered']==final['spent']==2 and {x['agent_uid'] for x in final['records']}=={23701,23702} and outcomes['direct-egress']=='BLOCKED'
        elif case=='writable-sink-mount':assert final['admitted']==0 and list(expected['sink_files'])==['2.body'] and outcomes['direct-write']=='SUCCEEDED'
        elif case=='trusted-role-uid-collision':assert final['halted'] and not expected['sink_files'] and outcomes['untrusted-admin-halt']=='SUCCEEDED'
        elif case=='concurrent-cap1':assert final['global_cap']==1 and final['spent']==final['delivered']==1 and outcomes['denied_contenders']==1
        elif case=='crash-retry':assert outcomes['after_crash']['unknown_commit']==1 and outcomes['after_crash']['delivered']==0 and final['delivered']==1 and len(expected['sink_files'])==1
        elif case=='halt-inflight':assert outcomes['inflight']['unknown_commit']==1 and final['halted'] and final['delivered']==1 and outcomes['new-post-halt-delivery']=='BLOCKED'
        else:
            drift=json.loads((dest/'drift/bundle.json').read_text());assert drift['verdict']=='UNASSURED' and any(o['detail']=='DRIFT' for o in drift['obligations'])
    cleanup=(output/'cleanup.txt').read_text();assert cleanup.strip()=='remaining cstack-r2 containers:'
    commands=json.loads((output/'commands.json').read_text())
    assert any(x['argv'][:4]==['docker','kill','-s','KILL'] and x['exit']==0 for x in commands)
    assert any(x['argv'][:3]==['docker','image','rm'] and x['exit']==0 for x in commands)
    print('PASS: raw daemon inventory, same scanned/started mounts and UIDs, SQLite backups, actual sink bytes, crash gap, dedup, HALT and cleanup')
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output');a=p.parse_args();check(a.output)
