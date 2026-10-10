#!/usr/bin/env python3
"""Regenerate synthetic fixtures; no real images or credentials are used."""
import copy
import hashlib
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from extractors.compose import collect, sha

def dumps(x): return json.dumps(x,sort_keys=True,indent=2)+'\n'
def build():
    base=ROOT/'examples/compose-two-agent'
    image='example.invalid/local-slice@sha256:'+'a'*64
    def mount(source,target,read_only=False): return {'type':'bind','source':source,'target':target,'read_only':read_only}
    c={'services':{},'networks':{'isolated':{'internal':True}},'x-cstack':{
       'sink_source':'/slice/sink','database_source':'/slice/db','budget':1,
       'broker_sha256':sha(ROOT/'trusted_stack/controller.py'),'receiver_sha256':sha(ROOT/'trusted_stack/outbox_receiver.py')}}
    for name,role,uid in [('agent-a','agent',23701),('agent-b','agent',23702),('broker','broker',23700),('receiver','receiver',23700),('reviewer','reviewer',23703),('approver','approver',23704)]:
        c['services'][name]={'x-cstack-role':role,'user':str(uid),'image':image,'environment':{},'networks':['isolated'],'volumes':[]}
    c['services']['broker']['volumes']=[mount('/slice/db','/private')]
    c['services']['receiver']['volumes']=[mount('/slice/db','/private'),mount('/slice/sink','/output')]
    for name in ('agent-a','agent-b','reviewer','approver','broker'):
        c['services'][name]['volumes'].append(mount('/slice/channel','/channel',read_only=name!='broker'))
    cases={'clean':c}
    def mutation(name):
        m=copy.deepcopy(c); cases[name]=m; return m
    mutation('writable-sink-mount')['services']['agent-a']['volumes'].append(mount('/slice/sink','/bypass'))
    mutation('agent-broker-db-access')['services']['agent-b']['volumes'].append(mount('/slice/db','/bypass'))
    mutation('trusted-role-uid-collision')['services']['agent-a']['user']='23700'
    mutation('privileged-container')['services']['agent-a']['privileged']=True
    m=mutation('host-network');m['services']['agent-b']['network_mode']='host';del m['services']['agent-b']['networks']
    m=mutation('alternate-deputy-sink-credentials')
    m['services']['deputy']={'x-cstack-role':'deputy','user':'23700','image':image,'environment':{'SINK_CREDENTIAL':'dummy-only'},'volumes':[mount('/slice/sink','/output')],'networks':['isolated']}
    mutation('unknown-feature')['services']['agent-a']['devices']=['/dev/example']
    expected={}
    for name,c in cases.items():
        p=base/(name+'.compose.json'); p.write_text(dumps(c))
        r={'services':{k:{'uid':int(v['user']),'image':v['image'],'mounts':v['volumes'],'networks':v.get('networks',[]),'env_names':sorted(v['environment'])} for k,v in c['services'].items()}}
        rp=base/(name+'.runtime.json'); rp.write_text(dumps(r))
        # Relative source paths make fixture provenance portable across clones.
        import os
        old=os.getcwd(); os.chdir(ROOT)
        try:
            ir=collect(p.relative_to(ROOT),rp.relative_to(ROOT),sha(p))
            for n in ir['sources']:
                n['source']=str(Path(n['source']).relative_to(ROOT)) if n['source'].startswith(str(ROOT)+'/') else n['source']
            for n in ir['nodes']+ir['edges']:
                prov=n['provenance']
                prov['source']=str(Path(prov['source']).relative_to(ROOT)) if prov['source'].startswith(str(ROOT)+'/') else prov['source']
            (ROOT/'security_ir/fixtures'/(name+'.json')).write_text(dumps(ir))
        finally: os.chdir(old)
        expected[name]={'compose_sha256':sha(p),'verdict':'CONDITIONAL' if name=='clean' else 'UNASSURED','bypass':None if name=='clean' else name}
    (base/'expected.json').write_text(dumps(expected))
if __name__=='__main__': build()
