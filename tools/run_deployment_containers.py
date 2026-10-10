#!/usr/bin/env python3
"""Run ONLY the three benign local-image fixtures; observe actual sink bytes.
Never launch runtime sockets, privileged, host-network, or arbitrary fixture input.
Docker default namespaces/seccomp and numeric UIDs, no Landlock claim.
"""
import argparse
import base64
import hashlib
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.collect_deployment_docker import capture
from extractors.compose import collect,sha
from security_ir.verifier import verify

BODY=b'exact-reviewed-two-agent-container-slice'
CASES=('clean','writable-sink-mount','trusted-role-uid-collision')

def run(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    pin=json.loads((ROOT/'examples/compose-two-agent/image-pin.json').read_text())
    state=Path(pin['host_root'])
    if state.parent != ROOT or state.name!='deployment-container-state': raise ValueError('state must be inside the authorized clone')
    if state.exists():raise ValueError('refusing existing experiment state')
    project='sol-pr45-followup';commands=[];results={}
    def cmd(args):
        p=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,timeout=60)
        commands.append({'argv':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
        if p.returncode:raise RuntimeError((args,p.stdout,p.stderr))
        return p.stdout
    def exec_code(service,code,*args):
        return cmd(['docker','compose','-p',project,'-f',str(compose),'exec','-T',service,'/usr/bin/python3','-c',code,*map(str,args)])
    def rpc(service,data,want):
        ans=json.loads(exec_code(service,"import json,sys;from trusted_stack.client import request;print(json.dumps(request('/channel/broker.sock',json.loads(sys.argv[1]))))",json.dumps(data)))
        assert ans['ok']==want,(service,data,ans)
        return ans
    def observe(dest):
        # Host sink observer copies the sink itself, never broker output/logs.
        cmd(['sudo','-n','cp','-a',str(state/'sink'),str(dest/'sink')])
        cmd(['sudo','-n','chown','-R',str(__import__('os').getuid()),str(dest/'sink')])
        files={p.name:{'sha256':sha(p),'body_b64':base64.b64encode(p.read_bytes()).decode(),'size':p.stat().st_size} for p in sorted((dest/'sink').iterdir()) if p.is_file()}
        (dest/'sink-state.json').write_text(json.dumps(files,sort_keys=True,indent=2)+'\n')
        return files
    compose=None
    try:
        # Docker daemon is an explicit TCB member, not attestation.
        (output/'docker-info.json').write_text(cmd(['docker','info','--format','{{json .}}']))
        for case in CASES:
            dest=output/case;dest.mkdir()
            compose=ROOT/'examples/compose-two-agent'/f'{case}.compose.json'
            c=json.loads(compose.read_text())
            # Fail before launch if the authorized benign experiment has been edited to grant host control.
            for s in c['services'].values():
                assert not s.get('privileged') and not s.get('network_mode')
                assert set(s)<={'x-cstack-role','user','image','environment','networks','volumes'}
                assert s['image']==pin['image']
                assert all(Path(v['source']).parent==state for v in s['volumes'])
            state.mkdir()
            for directory in ('db','sink','channel'):(state/directory).mkdir(mode=0o755)
            cmd(['sudo','-n','chown','23700:23700',str(state/'db'),str(state/'sink'),str(state/'channel')])
            cmd(['sudo','-n','chmod','700',str(state/'db'),str(state/'sink')])
            # Mutation has BOTH writable mount and writable sink permissions; mount
            # alone would still be stopped by Linux DAC. Permission change is captured.
            if case=='writable-sink-mount':cmd(['sudo','-n','chmod','777',str(state/'sink')])
            shutil.copyfile(compose,dest/'compose.json')
            cmd(['docker','compose','-p',project,'-f',str(compose),'up','-d','--pull','never'])
            for _ in range(200):
                if (state/'channel/broker.sock').exists():break
                time.sleep(.025)
            else:raise RuntimeError('container broker socket did not appear')
            runtime=capture(compose,project,dest)
            ir=collect(compose,dest/'runtime.json',sha(compose))
            (dest/'ir.json').write_text(json.dumps(ir,sort_keys=True,indent=2)+'\n')
            from tools.check_deployment_lean import check
            checked=check(ir);bundle=verify(ir)
            for o in bundle['obligations']:
                if o['premise']=='Lean-contract-instances':o.update(status='PROVEN_IN_MODEL' if checked['accepted'] else 'REFUTED',detail=checked['axioms'])
            bundle['lean']=checked
            bundle['verdict']='UNASSURED' if any(o['status'] in ('REFUTED','UNASSESSED') for o in bundle['obligations']) else 'CONDITIONAL'
            (dest/'bundle.json').write_text(json.dumps(bundle,sort_keys=True,indent=2)+'\n')
            assert bundle['verdict']==('CONDITIONAL' if case=='clean' else 'UNASSURED'),bundle
            if case=='clean':
                digest=hashlib.sha256(BODY).hexdigest();expiry=int(time.time())+900
                for agent,uid,nonce,lease in [('agent-a',23701,'a','lease-a'),('agent-b',23702,'b','lease-b')]:
                    rpc(agent,{'op':'stage','body_b64':base64.b64encode(BODY).decode()},True)
                    if agent=='agent-a':rpc('reviewer',{'op':'review','digest':digest},True)
                    rpc('broker',{'op':'issue_lease','lease_id':lease,'agent_uid':uid,'budget':1,'expires':expiry},True)
                    rpc('approver',{'op':'approve','nonce':nonce,'digest':digest,'destination':'metadata-only','agent_uid':uid,'lease_id':lease,'expires':expiry},True)
                req={'op':'effect_release','nonce':'a','digest':digest,'destination':'metadata-only','lease_id':'lease-a'}
                rpc('agent-a',req,True)
                reqb=dict(req,nonce='b',lease_id='lease-b');rpc('agent-b',reqb,False);rpc('agent-a',req,False)
                deliver="from pathlib import Path;from trusted_stack.controller import Controller,Principals;from trusted_stack.outbox_receiver import deliver_record;r=Principals(frozenset({23701,23702}),frozenset({23703}),frozenset({23704}),frozenset({23700}));print(deliver_record(Controller(Path('/private/gate.db'),r),1,Path('/output')))"
                exec_code('receiver',deliver)
                for agent in ('agent-a','agent-b'):
                    exec_code(agent,"from pathlib import Path\nassert not Path('/output').exists()\nassert not Path('/private/gate.db').exists()")
                files=observe(dest)
                assert list(files)==['1.body'] and base64.b64decode(files['1.body']['body_b64'])==BODY
                results[case]={'verdict':bundle['verdict'],'sink_files':files,'budget_second_agent_denied':True,'nonce_replay_denied':True,'direct_sink_and_database_unmounted':True}
            elif case=='writable-sink-mount':
                exec_code('agent-a',"import os;from pathlib import Path;p=Path('/bypass/2.body');f=p.open('xb');f.write(b'unapproved real container mount');f.flush();os.fsync(f.fileno());f.close()")
                files=observe(dest);assert list(files)==['2.body'] and base64.b64decode(files['2.body']['body_b64'])==b'unapproved real container mount'
                results[case]={'verdict':bundle['verdict'],'sink_files':files,'direct_agent_write':True,'sink_mode':'0777 (explicit DAC mutation in addition to RW bind)'}
            else:
                # Same UID has real ADMIN authority through SO_PEERCRED. No sink
                # mount is added: this particular mutation demonstrates trusted
                # authority confusion/HALT, not a fabricated direct file bypass.
                rpc('agent-a',{'op':'halt'},True)
                rpc('agent-b',{'op':'stage','body_b64':base64.b64encode(BODY).decode()},False)
                files=observe(dest);assert files=={}
                results[case]={'verdict':bundle['verdict'],'sink_files':files,'untrusted_agent_halt_accepted_as_admin':True,'subsequent_honest_task_denied':True,'direct_sink_write_demonstrated':False}
            (dest/'result.json').write_text(json.dumps(results[case],sort_keys=True,indent=2)+'\n')
            cmd(['docker','compose','-p',project,'-f',str(compose),'down','--volumes','--remove-orphans'])
            cmd(['sudo','-n','rm','-rf',str(state)])
        (output/'result.json').write_text(json.dumps({'scope':'real Docker containers: mounts and numeric UIDs, default Docker seccomp/namespaces; no Landlock or independent daemon attestation','image':pin['image'],'cases':results},sort_keys=True,indent=2)+'\n')
    finally:
        if compose is not None:
            cmd(['docker','compose','-p',project,'-f',str(compose),'down','--volumes','--remove-orphans'])
        if state.exists():cmd(['sudo','-n','rm','-rf',str(state)])
        (output/'commands.json').write_text(json.dumps(commands,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);a=ap.parse_args();run(a.output)
