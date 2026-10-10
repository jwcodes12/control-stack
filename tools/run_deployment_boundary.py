#!/usr/bin/env python3
"""Disposable cross-UID Linux boundary experiment; observer reads actual sink files.
Requires root for temporary process UIDs only. No accounts or real credentials.
Artifacts persist under --output; processes are always reaped. This is native
boundary evidence, not a launch/attestation of synthetic Compose images.
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
from tools.test_confined_effect_broker import drop_identity, by_uid
TRUSTED,A,B,REVIEWER,APPROVER=23700,23701,23702,23703,23704

def run(output):
    if os.geteuid()!=0: raise RuntimeError('root required for disposable process identities')
    output=output.resolve(); output.mkdir(mode=0o755,parents=True,exist_ok=False)
    worker=output/'worker'; shutil.copytree(ROOT/'trusted_stack',worker/'trusted_stack'); worker.chmod(0o755)
    dbdir=output/'private'; dbdir.mkdir(mode=0o700); os.chown(dbdir,TRUSTED,TRUSTED)
    sink=output/'sink'; sink.mkdir(mode=0o700); os.chown(sink,TRUSTED,TRUSTED)
    db=dbdir/'gate.db'; sock=output/'broker.sock'
    # Socket parent writable by trusted server, never by agent UIDs.
    os.chown(output,TRUSTED,TRUSTED)
    server=subprocess.Popen([sys.executable,'-m','trusted_stack.server','--db',str(db),'--socket',str(sock),'--agents',f'{A},{B}','--reviewers',str(REVIEWER),'--approvers',str(APPROVER),'--admins',str(TRUSTED),'--bootstrap-cap','1'],cwd=worker,preexec_fn=lambda:drop_identity(TRUSTED),stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)
    children=[]
    result={'scope':'native Linux broker/receiver boundary; synthetic Compose was not launched','uids':[TRUSTED,A,B,REVIEWER,APPROVER],'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (ROOT/'trusted_stack/controller.py',ROOT/'trusted_stack/server.py',ROOT/'trusted_stack/outbox_receiver.py',ROOT/'trusted_stack/agent_confinement.py',ROOT/'tools/run_deployment_boundary.py',ROOT/'tools/test_confined_effect_broker.py')},'cases':{}}
    def call(uid,data,allowed=True):
        res=by_uid(uid,worker,sock,data); assert res['ok'] is allowed,(data,res); return res
    def child(uid,code,*args):
        return subprocess.Popen([sys.executable,'-c',code,*map(str,args)],cwd=worker,preexec_fn=lambda:drop_identity(uid),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    def finish(p):
        out,err=p.communicate(timeout=20); assert p.returncode==0,(p.returncode,out,err); return out
    def observe(label):
        files={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'body_b64':base64.b64encode(p.read_bytes()).decode(),'size':p.stat().st_size} for p in sorted(sink.iterdir()) if p.is_file()}
        path=output/(label+'-sink.json'); path.write_text(json.dumps(files,indent=2,sort_keys=True)+'\n'); return files,str(path)
    try:
        for _ in range(200):
            if sock.exists(): break
            if server.poll() is not None: raise RuntimeError(server.stderr.read())
            time.sleep(.025)
        else: raise RuntimeError('broker did not start')
        body=b'exact-reviewed-two-agent-slice'; digest=hashlib.sha256(body).hexdigest(); expiry=int(time.time())+900
        for agent,nonce,lease in [(A,'a','lease-a'),(B,'b','lease-b')]:
            call(agent,{'op':'stage','body_b64':base64.b64encode(body).decode()})
            if agent==A: call(REVIEWER,{'op':'review','digest':digest})
            call(TRUSTED,{'op':'issue_lease','lease_id':lease,'agent_uid':agent,'budget':1,'expires':expiry})
            call(APPROVER,{'op':'approve','nonce':nonce,'digest':digest,'destination':'metadata-only','agent_uid':agent,'lease_id':lease,'expires':expiry})
        def confined(agent,nonce,lease,success):
            req={'op':'effect_release','nonce':nonce,'digest':digest,'destination':'metadata-only','lease_id':lease}
            source="import os,json,errno\n"
            source+=f"try: open({str(sink/'unauthorized.body')!r},'wb').write(b'bypass')\nexcept OSError as e: assert e.errno in (errno.EACCES,errno.EPERM)\nelse: raise RuntimeError('unmediated sink write')\n"
            source+=f"os.write(3,(json.dumps({req!r})+'\\n').encode())\na=json.loads(os.read(3,65536)); assert a['ok'] is {success!r},a\n"
            path=worker/f'agent-{agent}.py'; path.write_text(source); path.chmod(0o644)
            p=subprocess.Popen([sys.executable,'-m','trusted_stack.agent_confinement','--script',str(path),'--broker-socket',str(sock),'--broker-uid',str(TRUSTED)],cwd=worker,preexec_fn=lambda:drop_identity(agent),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True); children.append(p); finish(p)
        confined(A,'a','lease-a',True); confined(B,'b','lease-b',False); confined(A,'a','lease-a',False)
        # Pause a REAL receiver after durable sink publication, before receipt.
        published=output/'published.marker'; resume=output/'resume.marker'
        code='''import os,sys,time
from pathlib import Path
from trusted_stack.controller import Controller,Principals
from trusted_stack.outbox_receiver import deliver_record
roles=Principals(frozenset({23701,23702}),frozenset({23703}),frozenset({23704}),frozenset({23700}))
def pause():
 Path(sys.argv[3]).write_text('durably published')
 while not Path(sys.argv[4]).exists(): time.sleep(.02)
print(deliver_record(Controller(Path(sys.argv[1]),roles),1,Path(sys.argv[2]),after_publish=pause))
'''
        receiver=child(TRUSTED,code,db,sink,published,resume); children.append(receiver)
        for _ in range(300):
            if published.exists():break
            if receiver.poll() is not None:raise RuntimeError(receiver.communicate())
            time.sleep(.02)
        else:raise RuntimeError('publication marker absent')
        files,evidence=observe('clean-inflight'); assert list(files)==['1.body'] and files['1.body']['sha256']==digest
        halt_ready=output/'halt-ready.marker'
        haltcode="import sys,json; from pathlib import Path; from trusted_stack.client import request; Path(sys.argv[2]).write_text('HALT client ready before request'); print(json.dumps(request(sys.argv[1],{'op':'halt'})))"
        halt=child(TRUSTED,haltcode,sock,halt_ready); children.append(halt)
        for _ in range(300):
            if halt_ready.exists(): break
            if halt.poll() is not None: raise RuntimeError(halt.communicate())
            time.sleep(.02)
        else: raise RuntimeError('HALT client did not become ready')
        time.sleep(.15); assert halt.poll() is None,'HALT should wait for receiver SQLite writer lock'
        resume.write_text('continue'); finish(receiver); haltout=json.loads(finish(halt)); assert haltout['ok']
        files,evidence=observe('clean-after-halt'); assert list(files)==['1.body'] and files['1.body']['sha256']==digest
        blocked=child(TRUSTED,'''import sys
from pathlib import Path
from trusted_stack.controller import Controller,Principals,Denied
from trusted_stack.outbox_receiver import deliver_record
r=Principals(frozenset({23701,23702}),frozenset({23703}),frozenset({23704}),frozenset({23700}))
try: deliver_record(Controller(Path(sys.argv[1]),r),1,Path(sys.argv[2]))
except Denied: print('HALT denied delivery')
else: raise RuntimeError('post-HALT publication accepted')
''',db,sink); children.append(blocked); finish(blocked)
        result['cases']['clean']={'result':'PASS','sink_evidence':evidence,'files':files,'two_agents_shared_budget':True,'replay_denied':True,'halt_client_ready_before_receiver_release':True,'halt_during_inflight':'HALT waited for publication/receipt transaction; published bytes survive; new delivery denied'}
        # Mutation 1: writable sink permission is a bypass for an unconfined
        # helper. The existing launcher still denies writes with Landlock.
        sink.chmod(0o777)
        probe=child(A,"from pathlib import Path;import sys;Path(sys.argv[1]).write_bytes(b'unapproved writable sink mutation')",sink/'writable-mutation.body'); children.append(probe); finish(probe)
        source=worker/'writable-confined.py'; source.write_text(f"import errno\ntry: open({str(sink/'confined-mutation.body')!r},'wb').write(b'bad')\nexcept OSError as e: assert e.errno in (errno.EPERM,errno.EACCES)\nelse: raise RuntimeError('confinement failed')\n")
        p=subprocess.Popen([sys.executable,'-m','trusted_stack.agent_confinement','--script',str(source)],cwd=worker,preexec_fn=lambda:drop_identity(A),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);children.append(p);finish(p)
        files,evidence=observe('writable-sink-mount'); assert 'writable-mutation.body' in files and 'confined-mutation.body' not in files
        result['cases']['writable-sink-mount']={'result':'UNASSURED','sink_evidence':evidence,'direct_helper_bypass':True,'confined_write_denied':True,'limitation':'native mode/authority mutation corresponding to writable mount, not Docker bind-mount execution'}
        sink.chmod(0o700)
        # Mutation 2: agent assigned trusted owner UID; authenticated launcher
        # refuses a same-UID broker, but the agent has raw owner sink authority.
        p=subprocess.Popen([sys.executable,'-m','trusted_stack.agent_confinement','--script',str(source),'--broker-socket',str(sock),'--broker-uid',str(TRUSTED)],cwd=worker,preexec_fn=lambda:drop_identity(TRUSTED),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);children.append(p)
        out,err=p.communicate(timeout=20); assert p.returncode!=0
        probe=child(TRUSTED,"from pathlib import Path;import sys;Path(sys.argv[1]).write_bytes(b'unapproved UID collision mutation')",sink/'uid-collision.body');children.append(probe);finish(probe)
        files,evidence=observe('trusted-role-uid-collision'); assert 'uid-collision.body' in files
        result['cases']['trusted-role-uid-collision']={'result':'UNASSURED','sink_evidence':evidence,'direct_owner_bypass':True,'launcher_same_uid_rejected':True,'launcher_error':err.strip()}
        result['sink_directory']=str(sink); result['temporary_accounts_created']=False
        (output/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        print(json.dumps(result,indent=2,sort_keys=True))
    finally:
        for p in children+[server]:
            if p.poll() is None:p.terminate()
            try:p.communicate(timeout=5)
            except subprocess.TimeoutExpired:p.kill();p.communicate(timeout=5)
        # Remove every temporary trusted UID ownership and restore safe modes.
        for path in [output,*output.rglob('*')]:
            if not path.is_symlink():os.chown(path,0,0)
        sink.chmod(0o700)
        if sock.exists():sock.unlink()

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);a=ap.parse_args();run(a.output)
