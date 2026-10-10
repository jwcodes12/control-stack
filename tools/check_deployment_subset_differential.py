#!/usr/bin/env python3
"""T1.7: full Python/Lean agreement, not the superseded strict subset fallback."""
import argparse
import copy
import json
import random
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.kernel import check_many
from security_ir.verifier import verify

def configuration_accepted(ir):
    return not any(o['status'] in {'REFUTED','UNASSESSED'} and o['premise']!='Lean-contract-instances' for o in verify(ir)['obligations'])

def run(output=None):
    rng=random.Random(20261011)
    fixtures=[(p.stem,json.loads(p.read_text())) for p in sorted((ROOT/'security_ir/fixtures').glob('*.json'))]
    cases=[('fixture:'+name,ir) for name,ir in fixtures]
    kinds=['runtime-drift','uid','role','protected-edge','unknown-edge','privileged','host-network','clean']
    for i in range(250):
        fixture,base=rng.choice(fixtures);d=copy.deepcopy(base);kind=rng.choice(kinds)
        services=[n for n in d['nodes'] if n['type']=='service'];node=rng.choice(services);f=node['facts']
        if kind=='runtime-drift':f['runtime_match']=rng.choice(['MATCH','MISSING','DRIFT'])
        elif kind=='uid':f['uid']=rng.choice([None,0,23700,23701,23702,23703,23704,31000+rng.randrange(100)])
        elif kind=='role':f['role']=rng.choice(['agent','broker','receiver','reviewer','approver','deputy'])
        elif kind in {'protected-edge','unknown-edge'}:
            e=copy.deepcopy(d['edges'][0]);e.update({'from':node['id'],'to':rng.choice(['sink','database','unknown']),'capability':rng.choice(['write','read','call','escape','credential','opaque']),'reachability':'UNKNOWN' if kind=='unknown-edge' else 'PRESENT','authorization':rng.choice(['FORBIDDEN','PERMITTED','UNKNOWN']),'reason':'seeded differential mutation'})
            e['provenance']['kind']='UNKNOWN' if kind=='unknown-edge' else 'STATIC_INFERRED'
            key=lambda x:(x['from'],x['to'],x['capability'])
            d['edges']=[x for x in d['edges'] if key(x)!=key(e)]+[e]
        elif kind=='privileged':f['privileged']=True
        elif kind=='host-network':f['host_network']=True
        cases.append((f'{i}:{fixture}:{kind}',d))
    accepted,axioms=check_many([d for _,d in cases])
    rows=[{'case':name,'python_accepted':configuration_accepted(d),'lean_accepted':ok} for (name,d),ok in zip(cases,accepted)]
    mismatches=[r for r in rows if r['python_accepted']!=r['lean_accepted']]
    result={'seed':20261011,'fixtures':len(fixtures),'random_mutations':250,'kernel_certificates':len(cases),'mismatches':mismatches,'rows':rows}
    if output:
        Path(output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
        Path(output).with_suffix('.axioms.txt').write_text(axioms)
    assert not mismatches,mismatches
    print(f'PASS: {len(fixtures)} fixtures + 250 seeded random mutations; zero Python/Lean differences')
    return result
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output');a=ap.parse_args();run(a.output)
