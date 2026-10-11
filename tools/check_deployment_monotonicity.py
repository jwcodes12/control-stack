#!/usr/bin/env python3
"""Additive authority mutations of all predeclared fixtures (static only)."""
import argparse
import copy
import json
import random
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from extractors.compose import collect,sha
from tools.check_deployment_subset_differential import configuration_accepted

def run(output=None):
    rng=random.Random(20261012)
    base=ROOT/'examples/compose-two-agent'
    fixtures=sorted((ROOT/'security_ir/fixtures').glob('*.json'))
    kinds=['feature','mount','environment','capability','edge']
    rows=[]
    with tempfile.TemporaryDirectory(prefix='cstack-r2-monotonic-') as tmp:
        cp=Path(tmp)/'compose.json';rp=Path(tmp)/'runtime.json'
        for i in range(520):
            fixture=fixtures[i%len(fixtures)];name=fixture.stem
            before=json.loads(fixture.read_text());kind=kinds[i%len(kinds)]
            node=rng.choice([n['id'] for n in before['nodes'] if n['type']=='service'])
            if kind=='edge':
                after=copy.deepcopy(before)
                e=copy.deepcopy(next(e for e in before['edges'] if e['reachability']=='PRESENT'))
                target=rng.choice(['sink','database','unknown'])
                reach=rng.choice(['PRESENT','UNKNOWN'])
                e.update({'from':node,'to':target,'capability':'escape','reachability':reach,'authorization':'UNKNOWN','reason':'additive seeded authority'})
                e['provenance']['kind']='UNKNOWN' if reach=='UNKNOWN' else 'STATIC_INFERRED'
                # Preserve every existing edge; choose an unused authority key.
                occupied={(x['from'],x['to'],x['capability']) for x in after['edges']}
                for cap in ['escape','credential','read','write','call','opaque']:
                    if (node,target,cap) not in occupied:
                        e['capability']=cap;after['edges'].append(e);break
                else:raise AssertionError('no unused additive edge key')
            else:
                c=json.loads((base/(name+'.compose.json')).read_text())
                r=json.loads((base/(name+'.runtime.json')).read_text())
                service=c['services'][node];observed=r['services'].get(node,{})
                if kind=='feature':service['x-added-service-feature']=True
                elif kind=='mount':
                    mount={'type':'bind','source':'/slice/additive-'+str(i),'target':'/added-'+str(i),'read_only':False}
                    service['volumes'].append(mount);observed['mounts'].append(copy.deepcopy(mount))
                elif kind=='environment':
                    key=rng.choice(['PASSWORD','AUTH','PRIVATE','COOKIE','UNLISTED'])+'_'+str(i)
                    service['environment'][key]='synthetic';observed['env_names'].append(key)
                elif kind=='capability':service.setdefault('cap_add',[]).append('SYS_ADMIN')
                cp.write_text(json.dumps(c));rp.write_text(json.dumps(r));after=collect(cp,rp,sha(cp))
            was=configuration_accepted(before);now=configuration_accepted(after)
            assert not (not was and now),(name,kind,node)
            rows.append({'fixture':name,'addition':kind,'service':node,'before_accepted':was,'after_accepted':now})
    result={'seed':20261012,'mutations':len(rows),'negative_cases':sum(not r['before_accepted'] for r in rows),'false_improvements':0,'rows':rows,'scope':'strict additions to the 26 fixture configurations; no repair/removal; configuration obligations compared independently of pending Lean check'}
    if output:Path(output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(f'PASS: {len(rows)} seeded additions; no negative fixture becomes accepted')
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output');a=p.parse_args();run(a.output)
