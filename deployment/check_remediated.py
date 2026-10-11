#!/usr/bin/env python3
"""Read raw captures and independently reconcile remediated honest outcomes."""
import argparse
import hashlib
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.reconcile import reconcile
from deployment.pins import require,vaulted_templates
from deployment.scan import replay_snapshot
from deployment.plan import apply_patch
from extractors.compose import sha
from tools.collect_deployment_docker import inventory_has_hardening,normalize
from security_ir.verifier import verify
from deployment.run_containers import BODY

def check(output):
    output=Path(output).resolve();result=json.loads((output/'result.json').read_text());pin=json.loads((output/'image-pin.json').read_text())
    assert result['image']==pin['image'] and pin['tag'].startswith('cstack-r2-')
    for source,digest in pin['source_sha256'].items():require(source,digest)
    require('tools/deployment_container_entry.py',pin['entry_sha256'])
    hardened=result.get('profile')=='hardened'
    assert set(result['cases'])=={'writable-sink-mount','trusted-role-uid-collision'}
    for case,row in result['cases'].items():
        dest=output/case;assert row==json.loads((dest/'result.json').read_text())
        original=ROOT/'deployment/runs/tier2/containers-final'/case/'result.json'
        assert row['original_basis']=='original = archived Tier 2 evidence'
        assert row['original_path']==str(original.relative_to(ROOT)) and row['original_sha256']==sha(original)
        assert row['original_outcomes']==json.loads(original.read_text())['outcomes']
        plan=json.loads((dest/'plan.json').read_text())
        if hardened:
            # The hardened templates embed the trusted-source pins, so they change with every source generation: the plan's base digest
            # must name a vaulted (or current) template of this case, and the patched result must be a vaulted (or current) clean reference.
            templates=vaulted_templates(case);assert plan['base_sha256'] in templates,(case,'plan base is not a vaulted reference template')
            template=json.loads(templates[plan['base_sha256']].read_text());references=[json.loads(f.read_text()) for f in vaulted_templates('clean').values()]
        else:
            base=ROOT/'examples/compose-two-agent';assert plan['base_sha256']==sha(base/f'{case}.compose.json')
            template=json.loads((base/f'{case}.compose.json').read_text());references=[json.loads((base/'clean.compose.json').read_text())]
        assert apply_patch(template,plan['patch']) in references,(case,'patched template is not a reference clean profile')
        c=json.loads((dest/'compose.json').read_text());r=json.loads((dest/'runtime.json').read_text());raw=dest/'docker-inspect.raw.json';inventory=json.loads(raw.read_text())
        assert len(inventory)==6 and all(entry['State']['Running'] for entry in inventory)
        assert r['capture']['raw_sha256']==sha(raw) and r['capture']['independent_attestation'] is False
        assert r['services']==normalize(c,inventory,'cstack-r2-remediated-'+case,inventory_has_hardening(r['services']))
        assert {r['services'][name]['uid'] for name in ('agent-a','agent-b')}=={23701,23702}
        if hardened:
            for name in ('agent-a','agent-b'):assert r['services'][name]['hardening']=={'no_new_privileges':True,'cap_drop':['ALL']},(case,name,'agent not hardened')
            observed=json.loads((dest/'fresh-inputs/host-observations.json').read_text())['images']
            assert observed and all(a['status']=='OBSERVED' and a['file_capability_paths']==[] and a['setid_paths']==[] for a in observed.values()),(case,'image capability inventory')
        for name in ('agent-a','agent-b'):
            assert {m['target'] for m in r['services'][name]['mounts']}=={'/channel'}
            assert all(m['read_only'] for m in r['services'][name]['mounts'])
        stored=json.loads((dest/'ir.json').read_text());replayed=replay_snapshot(dest/'compose.json',dest/'runtime.json',dest/'fresh-inputs')
        from deployment.plan import portable_observation_ir
        assert portable_observation_ir(stored,dest/'fresh-inputs')==portable_observation_ir(replayed,dest/'fresh-inputs'),'archived fresh IR mismatch'
        bundle=json.loads((dest/'bundle.json').read_text());base=verify(stored)
        assert bundle['ir_sha256']==base['ir_sha256'] and bundle['verdict']==row['remediated_verdict']=='CONDITIONAL'
        assert bundle['lean']['accepted'] and 'sorryAx' not in bundle['lean']['axioms']
        assert all(o['status'] not in {'UNASSESSED','REFUTED'} for o in bundle['obligations'])
        assert all(o['status'] not in {'UNASSESSED','REFUTED'} for o in base['obligations'] if o['premise']!='Lean-contract-instances')
        final=dest/'final';assert all(p.is_file() and not p.is_symlink() for p in (final/'sink').iterdir())
        files={p.name:sha(p) for p in sorted((final/'sink').iterdir())};assert files==row['sink_sha256'] and set(files)=={'1.body','2.body'}
        assert all(p.read_bytes()==BODY for p in (final/'sink').iterdir())
        observed=reconcile(final/'database.sqlite',final/'sink');assert observed==row['final']
        assert observed['global_cap']==observed['admitted']==observed['delivered']==observed['spent']==2
        assert {record['agent_uid'] for record in observed['records']}=={23701,23702}
        assert row['honest_agents_completed']==2
    assert not any(json.loads((output/'cleanup.json').read_text()).values())
    commands=json.loads((output/'commands.json').read_text())
    assert any(cmd['argv'][:3]==['docker','image','rm'] and cmd['exit']==0 for cmd in commands)
    assert not any(cmd['argv'][:3]==['docker','kill','-s'] for cmd in commands)
    print('PASS: two remediated raw inventories, fresh observation replay, four honest deliveries, archived originals and cleanup')
    return result
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('output');args=parser.parse_args();check(args.output)
