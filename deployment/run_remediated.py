#!/usr/bin/env python3
"""Only two fixed remediated reference configurations; honest work only.
Original outcomes are archived Tier 2 evidence, never rerun here.
"""
import argparse
import base64
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.plan import build_plan,apply_patch
from deployment.collect_docker import capture
from deployment.scan import scan
from extractors.compose import collect,sha
from security_ir.verifier import verify,report
from tools.check_deployment_lean import check
from deployment.run_containers import BODY,PRINCIPALS,DELIVER,RPC
CASES=('writable-sink-mount','trusted-role-uid-collision')

def run(output,pin_path,legacy=False):
    """Default: the repair templates of the hardened profile, launched on the current source generation.
    legacy=True reproduces the archived Tier 5 run from the frozen legacy templates."""
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    pin=json.loads(Path(pin_path).read_text());state=Path(pin['host_root'])
    assert state==ROOT/'deployment-container-state' and not state.exists()
    assert pin['tag'].startswith('cstack-r2-')
    for source,digest in pin['source_sha256'].items():assert sha(ROOT/source)==digest
    assert sha(ROOT/'tools/deployment_container_entry.py')==pin['entry_sha256']
    (output/'image-pin.json').write_text(json.dumps(pin,sort_keys=True,indent=2)+'\n')
    commands=[];events=[];results={};compose=None;project=None;owned=False
    def cmd(argv,required=True):
        p=subprocess.run(list(map(str,argv)),cwd=ROOT,capture_output=True,text=True,timeout=60)
        commands.append({'argv':list(map(str,argv)),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
        if required and p.returncode:raise RuntimeError((argv,p.returncode,p.stdout,p.stderr))
        return p.stdout
    def dc(*args):return ['docker','compose','-p',project,'-f',str(compose),*map(str,args)]
    def execute(service,code,*args):return cmd(dc('exec','-T',service,'/usr/bin/python3','-c',code,*map(str,args)))
    def rpc(service,data):
        answer=json.loads(execute(service,RPC,json.dumps(data)));assert answer['ok'],answer
        events.append({'case':case,'service':service,'request':data,'response':answer});return answer
    try:
        image=json.loads(cmd(['docker','image','inspect',pin['image']]))[0]
        assert image['RepoTags'] and all(tag.startswith('cstack-r2-') for tag in image['RepoTags']);owned=True
        for case in CASES:
            dest=output/case;dest.mkdir();project='cstack-r2-remediated-'+case;compose=dest/'compose.json'
            base=ROOT/('examples/compose-two-agent' if legacy else 'examples/compose-two-agent-hardened');original=base/(case+'.compose.json');runtime=base/(case+'.runtime.json')
            c=json.loads(original.read_text());r=json.loads(runtime.read_text());ir=collect(original,runtime,sha(original),replay=legacy)
            plan=build_plan(c,r,ir,sha(original));candidate=apply_patch(c,plan['patch'])
            clean=json.loads((base/'clean.compose.json').read_text());assert candidate==clean,'launch only exact repaired clean profile'
            (dest/'plan.json').write_text(json.dumps(plan,sort_keys=True,indent=2)+'\n')
            old_root=candidate['x-cstack']['sink_source'].rsplit('/',1)[0]
            for key in ('sink_source','database_source','channel_source'):candidate['x-cstack'][key]=str(state)+candidate['x-cstack'][key][len(old_root):]
            candidate['x-cstack']['budget']=2
            for service in candidate['services'].values():
                service['image']=pin['image']
                assert not legacy or 'security_opt' not in service
                for mount in service['volumes']:
                    mount['source']=str(state)+mount['source'][len(old_root):]
                    assert Path(mount['source']).parent==state
            compose.write_text(json.dumps(candidate,sort_keys=True,indent=2)+'\n')
            state.mkdir()
            for directory in ('db','sink','channel'):(state/directory).mkdir(mode=0o755)
            (state/'db/cap').write_text('2')
            cmd(['sudo','-n','chown','-R','23700:23700',state]);cmd(['sudo','-n','chmod','700',state/'db',state/'sink'])
            cmd(dc('up','-d','--pull','never'))
            deadline=time.monotonic()+15
            while not (state/'channel/broker.sock').exists() and time.monotonic()<deadline:time.sleep(.05)
            assert (state/'channel/broker.sock').exists(),'broker startup timed out'
            capture(compose,project,dest)
            ir=scan(compose,dest/'runtime.json',sha(compose),dest/'fresh-inputs');lean=check(ir);bundle=verify(ir)
            for obligation in bundle['obligations']:
                if obligation['premise']=='Lean-contract-instances':obligation.update(status='PROVEN_IN_MODEL' if lean['accepted'] else 'REFUTED',detail=lean['axioms'])
            bundle['lean']=lean;bundle['verdict']='UNASSURED' if any(o['status'] in {'REFUTED','UNASSESSED'} for o in bundle['obligations']) else 'CONDITIONAL'
            assert bundle['verdict']=='CONDITIONAL',bundle
            for name,value in [('ir',ir),('bundle',bundle)]:(dest/(name+'.json')).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
            (dest/'report.md').write_text(report(bundle))
            digest=hashlib.sha256(BODY).hexdigest();expires=int(time.time())+1800
            for index,(agent,uid) in enumerate((('agent-a',23701),('agent-b',23702)),1):
                lease='honest-'+agent;nonce='honest-'+agent
                rpc(agent,{'op':'stage','body_b64':base64.b64encode(BODY).decode()})
                if index==1:rpc('reviewer',{'op':'review','digest':digest})
                rpc('broker',{'op':'issue_lease','lease_id':lease,'agent_uid':uid,'budget':1,'expires':expires})
                rpc('approver',{'op':'approve','nonce':nonce,'digest':digest,'destination':'metadata-only','agent_uid':uid,'lease_id':lease,'expires':expires})
                rpc(agent,{'op':'effect_release','nonce':nonce,'digest':digest,'destination':'metadata-only','lease_id':lease})
                execute('receiver',DELIVER+f"print(deliver_record(controller,{index},Path('/output')))")
            final=dest/'final';final.mkdir()
            cmd(['sudo','-n','cp','-a',state/'sink',final/'sink']);cmd(['sudo','-n','chown','-R',os.getuid(),final/'sink'])
            backup="import sqlite3,sys;s=sqlite3.connect('file:'+sys.argv[1]+'?mode=ro',uri=True);t=sqlite3.connect(sys.argv[2]);s.backup(t);t.close();s.close()"
            cmd(['sudo','-n','python3','-c',backup,state/'db/gate.db',final/'database.sqlite']);cmd(['sudo','-n','chown',os.getuid(),final/'database.sqlite'])
            from deployment.reconcile import reconcile
            actual=reconcile(final/'database.sqlite',final/'sink');assert actual['delivered']==actual['admitted']==actual['spent']==2
            assert {record['agent_uid'] for record in actual['records']}=={23701,23702}
            files={p.name:sha(p) for p in sorted((final/'sink').iterdir())};assert len(files)==2
            assert all(p.read_bytes()==BODY for p in (final/'sink').iterdir())
            original_path=ROOT/'deployment/runs/tier2/containers-final'/case/'result.json'
            results[case]={'original_basis':'original = archived Tier 2 evidence','original_path':str(original_path.relative_to(ROOT)),'original_sha256':sha(original_path),'original_outcomes':json.loads(original_path.read_text())['outcomes'],'remediated_verdict':bundle['verdict'],'honest_agents_completed':2,'final':actual,'sink_sha256':files,'scope':'UIDs and mounts match fresh daemon capture; private custody observed. No new bypass probes; absence of a mount is configuration evidence, not a fresh denial experiment.'}
            (dest/'result.json').write_text(json.dumps(results[case],sort_keys=True,indent=2)+'\n')
            cmd(dc('down','--volumes','--remove-orphans'));cmd(['sudo','-n','rm','-rf',state])
        (output/'result.json').write_text(json.dumps({'image':pin['image'],'cases':results,'scope':'Honest tasks on remediated configurations only; originals archived Tier 2.',**({} if legacy else {'profile':'hardened'})},sort_keys=True,indent=2)+'\n')
    finally:
        if compose is not None:cmd(dc('down','--volumes','--remove-orphans'),False)
        if state.exists():cmd(['sudo','-n','rm','-rf',state])
        if owned:cmd(['docker','image','rm',pin['image']],False)
        remaining={kind:cmd(argv) for kind,argv in {'containers':['docker','ps','-a','--filter','name=cstack-r2-','--format','{{.Names}}'],'networks':['docker','network','ls','--filter','name=cstack-r2-','--format','{{.Name}}'],'images':['docker','image','ls','--filter','reference=cstack-r2-*','--format','{{.Repository}}:{{.Tag}}'],'volumes':['docker','volume','ls','--filter','name=cstack-r2-','--format','{{.Name}}']}.items()}
        (output/'cleanup.json').write_text(json.dumps(remaining,sort_keys=True,indent=2)+'\n')
        (output/'commands.json').write_text(json.dumps(commands,sort_keys=True,indent=2)+'\n');(output/'events.json').write_text(json.dumps(events,sort_keys=True,indent=2)+'\n')
        assert not any(remaining.values()),remaining
    print('PASS: two fixed remediated configurations, four honest completions; originals archived; own resources removed')
    return results
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);parser.add_argument('--pin',required=True);parser.add_argument('--legacy',action='store_true');args=parser.parse_args();run(args.output,args.pin,args.legacy)
