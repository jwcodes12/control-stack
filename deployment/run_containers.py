#!/usr/bin/env python3
"""Fixed benign R2 Docker experiments; never accepts arbitrary launch fixtures."""
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
from deployment.collect_docker import capture
from extractors.compose import collect,sha
from security_ir.verifier import verify,report
from tools.check_deployment_lean import check
BODY=b'exact-reviewed-r2-agent-task'
CASES=('clean','writable-sink-mount','trusted-role-uid-collision','concurrent-cap1','crash-retry','halt-inflight','drift-uid')
PRINCIPALS="Principals(frozenset({23701,23702}),frozenset({23703}),frozenset({23704}),frozenset({23700}))"
DELIVER="from pathlib import Path;from trusted_stack.controller import Controller,Principals;from trusted_stack.outbox_receiver import deliver_record;controller=Controller(Path('/private/gate.db'),"+PRINCIPALS+")\n"
RPC="import json,sys;from trusted_stack.client import request;print(json.dumps(request('/channel/broker.sock',json.loads(sys.argv[1]))))"

def run(output,pin_path=None):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    pin=json.loads(Path(pin_path or ROOT/'examples/compose-two-agent/image-pin.json').read_text())
    state=Path(pin['host_root'])
    assert state.parent==ROOT and state.name=='deployment-container-state' and not state.exists()
    assert pin['tag'].startswith('cstack-r2-')
    for path,digest in pin['source_sha256'].items():assert sha(ROOT/path)==digest
    assert sha(ROOT/'tools/deployment_container_entry.py')==pin['entry_sha256']
    (output/'image-pin.json').write_text(json.dumps(pin,sort_keys=True,indent=2)+'\n')
    shutil.copyfile(ROOT/'tools/deployment_container_entry.py',output/'container-entry.py')
    commands=[];events=[];results={};compose=None;project=None;children=[];image_owned=False
    def cmd(argv,check_exit=True):
        start=time.monotonic();p=subprocess.run(list(map(str,argv)),cwd=ROOT,text=True,capture_output=True,timeout=60)
        commands.append({'argv':list(map(str,argv)),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'started_monotonic':start,'ended_monotonic':time.monotonic()})
        if check_exit and p.returncode:raise RuntimeError((argv,p.returncode,p.stdout,p.stderr))
        return p
    def dc(*args):return ['docker','compose','-p',project,'-f',str(compose),*map(str,args)]
    def argv_code(service,code,*args):return dc('exec','-T',service,'/usr/bin/python3','-c',code,*map(str,args))
    def execute(service,code,*args):return cmd(argv_code(service,code,*args)).stdout
    def rpc(service,data,want=True):
        ans=json.loads(execute(service,RPC,json.dumps(data)));events.append({'case':case,'service':service,'request':data,'response':ans})
        if want is not None:assert ans['ok']==want,(service,data,ans)
        return ans
    def spawn(argv):
        p=subprocess.Popen(argv,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);children.append((p,argv,time.monotonic()));return p
    def finish(p,expected_exit=0):
        stdout,stderr=p.communicate(timeout=15);_,argv,start=next(x for x in children if x[0] is p)
        commands.append({'argv':argv,'exit':p.returncode,'stdout':stdout,'stderr':stderr,'started_monotonic':start,'ended_monotonic':time.monotonic()})
        if expected_exit is not None:assert p.returncode==expected_exit,(argv,stdout,stderr,p.returncode)
        return stdout
    def wait_marker(name):
        deadline=time.monotonic()+10
        while time.monotonic()<deadline:
            if cmd(['sudo','-n','test','-f',state/'db'/name],False).returncode==0:return
            time.sleep(.03)
        raise TimeoutError('receiver marker '+name)
    def sink_snapshot(dest):
        dest.mkdir(parents=True,exist_ok=True);cmd(['sudo','-n','cp','-a',state/'sink',dest/'sink']);cmd(['sudo','-n','chown','-R',os.getuid(),dest/'sink'])
        assert all(p.is_file() and not p.is_symlink() for p in (dest/'sink').iterdir()),'unexpected nonregular sink entry'
        actual={p.name:{'sha256':sha(p),'body_b64':base64.b64encode(p.read_bytes()).decode(),'size':p.stat().st_size} for p in sorted((dest/'sink').iterdir()) if p.is_file()}
        if not actual:(dest/'sink/.gitkeep').touch()
        (dest/'sink-state.json').write_text(json.dumps(actual,sort_keys=True,indent=2)+'\n');return actual
    def observe(dest):
        files=sink_snapshot(dest)
        value=json.loads(cmd(['sudo','-n','python3',ROOT/'deployment/reconcile.py','--db',state/'db/gate.db','--sink',state/'sink']).stdout)
        (dest/'reconciliation.json').write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
        backup="import sqlite3,sys;source=sqlite3.connect('file:'+sys.argv[1]+'?mode=ro',uri=True);target=sqlite3.connect(sys.argv[2]);source.backup(target);target.close();source.close()"
        cmd(['sudo','-n','python3','-c',backup,state/'db/gate.db',dest/'database.sqlite']);cmd(['sudo','-n','chown',os.getuid(),dest/'database.sqlite'])
        return files,value
    def scan(dest):
        capture(compose,project,dest);ir=collect(compose,dest/'runtime.json',sha(compose));checked=check(ir);bundle=verify(ir)
        for o in bundle['obligations']:
            if o['premise']=='Lean-contract-instances':o.update(status='PROVEN_IN_MODEL' if checked['accepted'] else 'REFUTED',detail=checked['axioms'])
        bundle['lean']=checked;bundle['verdict']='UNASSURED' if any(o['status'] in {'REFUTED','UNASSESSED'} for o in bundle['obligations']) else 'CONDITIONAL'
        (dest/'ir.json').write_text(json.dumps(ir,sort_keys=True,indent=2)+'\n');(dest/'bundle.json').write_text(json.dumps(bundle,sort_keys=True,indent=2)+'\n');(dest/'report.md').write_text(report(bundle))
        return ir,bundle
    def prepare_agents():
        digest=hashlib.sha256(BODY).hexdigest();expires=int(time.time())+1800;requests={}
        for agent,uid,nonce,lease in [('agent-a',23701,'a','lease-a'),('agent-b',23702,'b','lease-b')]:
            rpc(agent,{'op':'stage','body_b64':base64.b64encode(BODY).decode()})
            if agent=='agent-a':rpc('reviewer',{'op':'review','digest':digest})
            rpc('broker',{'op':'issue_lease','lease_id':lease,'agent_uid':uid,'budget':1,'expires':expires})
            rpc('approver',{'op':'approve','nonce':nonce,'digest':digest,'destination':'metadata-only','agent_uid':uid,'lease_id':lease,'expires':expires})
            requests[agent]={'op':'effect_release','nonce':nonce,'digest':digest,'destination':'metadata-only','lease_id':lease}
        return requests
    try:
        image=json.loads(cmd(['docker','image','inspect',pin['image']]).stdout)[0]
        assert image['RepoTags'] and all(x.startswith('cstack-r2-') for x in image['RepoTags'])
        image_owned=True
        (output/'docker-info.json').write_text(cmd(['docker','info','--format','{{json .}}']).stdout)
        (output/'selinux.txt').write_text('Host: '+cmd(['getenforce']).stdout+'Docker security options: '+cmd(['docker','info','--format','{{json .SecurityOptions}}']).stdout+'All disposable binds use shared z, never private Z on shared directories; daemon currently does not advertise SELinux enforcement. No host-wide relabel or LSM change.\n')
        for case in CASES:
            dest=output/case;dest.mkdir();project='cstack-r2-'+case;compose=dest/'compose.json'
            template=case if case in CASES[:3] else 'clean';c=json.loads((ROOT/'examples/compose-two-agent'/f'{template}.compose.json').read_text())
            old_root=c['x-cstack']['sink_source'].rsplit('/',1)[0]
            for key in ('sink_source','database_source','channel_source'):c['x-cstack'][key]=str(state)+c['x-cstack'][key][len(old_root):]
            c['x-cstack']['budget']=2 if case=='clean' else 1
            for service in c['services'].values():
                service['image']=pin['image']
                assert not service.get('privileged') and not service.get('network_mode')
                assert set(service)<={'x-cstack-role','user','image','environment','networks','volumes'}
                for mount in service['volumes']:
                    assert mount['type']=='bind' and type(mount['read_only']) is bool
                    assert mount['source'].startswith(old_root+'/')
                    mount['source']=str(state)+mount['source'][len(old_root):]
                    assert Path(mount['source']).parent==state and mount.get('bind')=={'selinux':'z'}
            assert c['networks']=={'isolated':{'internal':True}}
            compose.write_text(json.dumps(c,sort_keys=True,indent=2)+'\n')
            state.mkdir()
            for d in ('db','sink','channel'):(state/d).mkdir(mode=0o755)
            (state/'db/cap').write_text(str(c['x-cstack']['budget']))
            cmd(['sudo','-n','chown','-R','23700:23700',state]);cmd(['sudo','-n','chmod','700',state/'db',state/'sink'])
            if case=='writable-sink-mount':cmd(['sudo','-n','chmod','777',state/'sink'])
            cmd(dc('up','-d','--pull','never'))
            deadline=time.monotonic()+10
            while not (state/'channel/broker.sock').exists() and time.monotonic()<deadline:time.sleep(.03)
            assert (state/'channel/broker.sock').exists(),'broker startup timeout'
            ir,bundle=scan(dest);prediction=bundle['verdict'];assert prediction==('UNASSURED' if template!='clean' else 'CONDITIONAL')
            outcomes={}
            if case=='writable-sink-mount':
                execute('agent-a',"import os;from pathlib import Path;f=Path('/bypass/2.body').open('xb');f.write(b'unapproved r2 direct write');f.flush();os.fsync(f.fileno());f.close()")
                outcomes={'direct-write':'SUCCEEDED','sink_mode':'0777; explicit DAC mutation plus RW bind'}
            elif case=='trusted-role-uid-collision':
                rpc('agent-a',{'op':'halt'});rpc('agent-b',{'op':'stage','body_b64':base64.b64encode(BODY).decode()},False)
                outcomes={'untrusted-admin-halt':'SUCCEEDED','subsequent-honest-task':'BLOCKED','direct-sink-write':'UNOBSERVED'}
            elif case=='drift-uid':
                changed=json.loads(json.dumps(c));changed['services']['agent-a']['user']='23705';changed_path=dest/'drift-launch.compose.json';changed_path.write_text(json.dumps(changed,sort_keys=True,indent=2)+'\n')
                cmd(['docker','compose','-p',project,'-f',str(changed_path),'up','-d','--pull','never','--no-deps','--force-recreate','agent-a'])
                drift=dest/'drift';drift.mkdir();drift_ir,drift_bundle=scan(drift)
                assert drift_bundle['verdict']=='UNASSURED' and next(n['facts']['runtime_match'] for n in drift_ir['nodes'] if n['id']=='agent-a')=='DRIFT'
                outcomes={'running-uid-drift':'SUCCEEDED','new_verdict':'UNASSURED','old_report_invalidated':True}
            else:
                requests=prepare_agents()
                if case=='concurrent-cap1':
                    race="import json,sys,time;from pathlib import Path;from trusted_stack.client import request;print('READY',flush=True)\nwhile not Path('/channel/race-go').exists():time.sleep(.01)\nprint(json.dumps(request('/channel/broker.sock',json.loads(sys.argv[1]))))"
                    contenders=[spawn(argv_code(a,race,json.dumps(req))) for a,req in requests.items()]
                    for p in contenders:assert p.stdout.readline().strip()=='READY'
                    cmd(['sudo','-n','touch',state/'channel/race-go'])
                    answers=[json.loads(finish(p).strip()) for p in contenders];assert sum(a['ok'] for a in answers)==1
                    for (agent,request),answer in zip(requests.items(),answers):events.append({'case':case,'service':agent,'request':request,'response':answer,'concurrent':True})
                    execute('receiver',DELIVER+"print(deliver_record(controller,1,Path('/output')))")
                    outcomes={'concurrent-double-spend':'BLOCKED','accepted_contenders':1,'denied_contenders':1}
                else:
                    rpc('agent-a',requests['agent-a']);rpc('agent-a',requests['agent-a'],False);outcomes['nonce-replay']='BLOCKED'
                    if case=='clean':
                        rpc('agent-b',requests['agent-b'])
                        for rid in (1,2):execute('receiver',DELIVER+f"print(deliver_record(controller,{rid},Path('/output')))")
                        outcomes['honest-agents']={'agent-a':'SUCCEEDED','agent-b':'SUCCEEDED'}
                        denied=execute('agent-a',"import json,socket\ns=socket.socket();s.settimeout(1)\ntry:s.connect(('192.0.2.1',9));print(json.dumps({'connected':True}))\nexcept OSError as e:print(json.dumps({'connected':False,'error':str(e)}))\nassert not any(line.split()[1]=='00000000' for line in open('/proc/net/route').readlines()[1:])")
                        assert json.loads(denied)['connected'] is False;outcomes['direct-egress']='BLOCKED';outcomes['egress_probe']=json.loads(denied)
                    else:
                        hook="def hook():\n Path('/private/published-ready').write_text('durable publication before receipt')\n while not Path('/private/publish-go').exists():time.sleep(.01)\n"
                        worker=spawn(argv_code('receiver',DELIVER+'import time\n'+hook+"print(deliver_record(controller,1,Path('/output'),after_publish=hook))"))
                        wait_marker('published-ready')
                        _,inflight=observe(dest/'inflight');assert inflight['admitted']==1 and inflight['delivered']==0 and inflight['unknown_commit']==1
                        if case=='crash-retry':
                            receiver_id=cmd(dc('ps','-q','receiver')).stdout.strip();cmd(['docker','kill','-s','KILL',receiver_id]);finish(worker,None)
                            _,crashed=observe(dest/'after-crash');assert crashed['unknown_commit']==1 and crashed['delivered']==0
                            cmd(['docker','start',receiver_id]);execute('receiver',DELIVER+"print(deliver_record(controller,1,Path('/output')))")
                            execute('receiver',DELIVER+"print(deliver_record(controller,1,Path('/output')))")
                            post_restart=dest/'post-restart';post_restart.mkdir();_,post_bundle=scan(post_restart);assert post_bundle['verdict']=='CONDITIONAL'
                            outcomes.update({'post_restart_reverified':True,'crash-before-receipt':'SUCCEEDED','restart-deduplicated-retry':'SUCCEEDED','inflight':inflight,'after_crash':crashed})
                        else:
                            halt=spawn(argv_code('broker',RPC,json.dumps({'op':'halt'})));time.sleep(.2);assert halt.poll() is None,'HALT failed to serialize with publication'
                            cmd(['sudo','-n','touch',state/'db/publish-go']);finish(worker);halt_answer=json.loads(finish(halt));assert halt_answer['ok']
                            events.append({'case':case,'service':'broker','request':{'op':'halt'},'response':halt_answer})
                            denied=execute('receiver',DELIVER+"from trusted_stack.controller import Denied\ntry:deliver_record(controller,1,Path('/output'));raise AssertionError('post-HALT delivery succeeded')\nexcept Denied:print('HALT blocks subsequent delivery')")
                            outcomes.update({'halt-during-inflight':'SUCCEEDED','new-post-halt-delivery':'BLOCKED','inflight':inflight})
            files,final=observe(dest/'final')
            if case=='clean':assert len(files)==2 and final['delivered']==2 and {r['agent_uid'] for r in final['records']}=={23701,23702}
            if case in {'concurrent-cap1','crash-retry','halt-inflight'}:assert len(files)==1 and final['admitted']==final['delivered']==final['spent']==1
            if case=='writable-sink-mount':assert list(files)==['2.body'] and final['admitted']==0
            if case in {'trusted-role-uid-collision','drift-uid'}:assert not files
            for f in files.values():assert base64.b64decode(f['body_b64'])==(b'unapproved r2 direct write' if case=='writable-sink-mount' else BODY)
            results[case]={'prediction':prediction,'outcomes':outcomes,'final':final,'sink_files':files,'agreement':True}
            (dest/'result.json').write_text(json.dumps(results[case],sort_keys=True,indent=2)+'\n')
            cmd(dc('down','--volumes','--remove-orphans'));cmd(['sudo','-n','rm','-rf',state])
        (output/'result.json').write_text(json.dumps({'scope':'real Docker, default namespaces/seccomp and numeric UIDs; daemon facts are not attestation; no host Landlock claim','image':pin['image'],'cases':results},sort_keys=True,indent=2)+'\n')
    finally:
        for p,argv,_ in children:
            if p.poll() is None:p.terminate()
        if compose is not None:cmd(dc('down','--volumes','--remove-orphans'),False)
        if state.exists():cmd(['sudo','-n','rm','-rf',state])
        if image_owned:cmd(['docker','image','rm',pin['image']],False)
        (output/'commands.json').write_text(json.dumps(commands,sort_keys=True,indent=2)+'\n')
        (output/'events.json').write_text(json.dumps(events,sort_keys=True,indent=2)+'\n')
        left=cmd(['docker','ps','-a','--filter','name=cstack-r2-','--format','{{.Names}}']).stdout
        networks=cmd(['docker','network','ls','--filter','name=cstack-r2-','--format','{{.Name}}']).stdout
        images=cmd(['docker','image','ls','--filter','reference=cstack-r2-*','--format','{{.Repository}}:{{.Tag}}']).stdout
        volumes=cmd(['docker','volume','ls','--filter','name=cstack-r2-','--format','{{.Name}}']).stdout
        (output/'cleanup.txt').write_text('remaining cstack-r2 containers:\n'+left+'\n'+networks+'\n'+images+'\n'+volumes)
        (output/'commands.json').write_text(json.dumps(commands,sort_keys=True,indent=2)+'\n')
        assert not (left or networks or images or volumes),'R2 resources remain'
    print('PASS: seven safe real-container cases, independent sink reconciliation, resources removed')
    return results
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--pin');a=p.parse_args();run(a.output,a.pin)
