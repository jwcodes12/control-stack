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
    pin=json.loads((base/'image-pin.json').read_text())
    image=pin['image']
    host_root=pin['host_root']
    def mount(source,target,read_only=False): return {'type':'bind','source':source,'target':target,'read_only':read_only}
    c={'services':{},'networks':{'isolated':{'internal':True}},'x-cstack':{
       'sink_source':host_root+'/sink','database_source':host_root+'/db','channel_source':host_root+'/channel','budget':1,
       'broker_sha256':sha(ROOT/'trusted_stack/controller.py'),'receiver_sha256':sha(ROOT/'trusted_stack/outbox_receiver.py')}}
    for name,role,uid in [('agent-a','agent',23701),('agent-b','agent',23702),('broker','broker',23700),('receiver','receiver',23700),('reviewer','reviewer',23703),('approver','approver',23704)]:
        c['services'][name]={'x-cstack-role':role,'user':str(uid),'image':image,'environment':{'SLICE_ROLE':name,'PYTHONPATH':'/slice'},'networks':['isolated'],'volumes':[]}
    c['services']['broker']['volumes']=[mount(host_root+'/db','/private')]
    c['services']['receiver']['volumes']=[mount(host_root+'/db','/private'),mount(host_root+'/sink','/output')]
    for name in ('agent-a','agent-b','reviewer','approver','broker'):
        c['services'][name]['volumes'].append(mount(host_root+'/channel','/channel',read_only=name!='broker'))
    cases={'clean':c}
    def mutation(name):
        m=copy.deepcopy(c); cases[name]=m; return m
    mutation('writable-sink-mount')['services']['agent-a']['volumes'].append(mount(host_root+'/sink','/bypass'))
    mutation('agent-broker-db-access')['services']['agent-b']['volumes'].append(mount(host_root+'/db','/bypass'))
    mutation('trusted-role-uid-collision')['services']['agent-a']['user']='23700'
    mutation('privileged-container')['services']['agent-a']['privileged']=True
    m=mutation('host-network');m['services']['agent-b']['network_mode']='host';del m['services']['agent-b']['networks']
    m=mutation('alternate-deputy-sink-credentials')
    m['services']['deputy']={'x-cstack-role':'deputy','user':'23700','image':image,'environment':{'SINK_CREDENTIAL':'dummy-only'},'volumes':[mount(host_root+'/sink','/output')],'networks':['isolated']}
    mutation('unknown-feature')['services']['agent-a']['devices']=['/dev/example']
    mutation('runtime-socket-mount')['services']['agent-a']['volumes'].append(mount('/var/run/docker.sock','/var/run/docker.sock'))
    mutation('trusted-source-mount')['services']['agent-a']['volumes'].append(mount('/slice/trusted_stack','/code'))
    mutation('unlisted-host-mount')['services']['agent-a']['volumes'].append(mount('/slice/benign','/benign'))
    mutation('writable-channel-mount')['services']['agent-a']['volumes'][-1]['read_only']=False
    mutation('channel-target-shadow')['services']['agent-a']['volumes'][-1]['target']='/etc'
    mutation('credential-password')['services']['agent-a']['environment']['PASSWORD']='dummy-only'
    mutation('unlisted-environment')['services']['agent-a']['environment']['LOGIN']='dummy-only'
    mutation('missing-isolated-network')['services']['agent-a']['networks']=[]
    mutation('mount-parent-alias')['services']['agent-a']['volumes'][-1]['source']=host_root+'/channel/../channel'
    mutation('trusted-reviewer-uid-collision')['services']['agent-a']['user']='23703'
    mutation('missing-reviewer-role')['services']['reviewer']['x-cstack-role']='approver'
    runtime_edits = {
        'runtime-alias': ('top','aliases', {'channel':'sink'}),
        'inherited-descriptor': ('service','inherited_fds', [3]),
        'injected-helper': ('top','injected_processes', ['host-helper']),
        'runtime-code-tamper': ('service','code_sha256', '0'*64),
        'daemon-uid-remap': ('top','uid_mapping', 'uninspected'),
        'storage-rollback': ('top','storage_epoch', 'uninspected'),
        'post-capture-drift': ('service','uid', 0),
    }
    for name in runtime_edits: mutation(name)
    expected={}
    for name,c in cases.items():
        p=base/(name+'.compose.json'); p.write_text(dumps(c))
        r={'services':{k:{'uid':int(v['user']),'image':v['image'],'mounts':sorted(v['volumes'],key=lambda m:(m['source'],m['target'])),'networks':v.get('networks',[]),'env_names':sorted(v['environment'])} for k,v in c['services'].items()}}
        if name in runtime_edits:
            section,key,value=runtime_edits[name]
            (r if section=='top' else r['services']['agent-a'])[key]=value
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
        expected[name]={'compose_sha256':sha(p),'verdict':'CONDITIONAL' if name=='clean' else 'UNASSURED','lean_accepted':name=='clean' or name in {'trusted-reviewer-uid-collision','missing-reviewer-role'} or (name in runtime_edits and runtime_edits[name][0]=='service'),'bypass':None if name=='clean' else {'writable-channel-mount':'unlisted-host-mount','channel-target-shadow':'unlisted-host-mount','credential-password':'opaque-credential-env-name:PASSWORD','missing-isolated-network':'unsupported service networks','mount-parent-alias':'unresolved mount source','trusted-reviewer-uid-collision':'trusted-role-uid-collision','missing-reviewer-role':'supported-roles'}.get(name, ('DRIFT' if runtime_edits[name][0]=='service' else 'unsupported/extra runtime service') if name in runtime_edits else name)}
    (base/'expected.json').write_text(dumps(expected))
if __name__=='__main__': build()
