"""Reviewable reference-profile remediation; never mutates input files or runtime facts."""
import hashlib
from deployment.pins import generations
from deployment.scan import reference_policy
from security_ir.verifier import verify
import copy
import difflib
import json
from pathlib import Path

def escape(s):return str(s).replace('~','~0').replace('/','~1')
def patch_diff(old,new,path=''):
    if old==new:return []
    if isinstance(old,dict) and isinstance(new,dict):
        result=[{'op':'remove','path':path+'/'+escape(k)} for k in sorted(old.keys()-new.keys())]
        for k in sorted(new):
            if k not in old:result.append({'op':'add','path':path+'/'+escape(k),'value':new[k]})
            else:result+=patch_diff(old[k],new[k],path+'/'+escape(k))
        return result
    if isinstance(old,list) and isinstance(new,list):
        # Pure deletion uses individual descending indexes, never replaces all mounts.
        j=0;keep=[]
        for i,value in enumerate(old):
            if j<len(new) and value==new[j]:keep.append(i);j+=1
        if j==len(new):return [{'op':'remove','path':path+'/'+str(i)} for i in reversed(range(len(old))) if i not in keep]
        if len(old)==len(new):return sum((patch_diff(a,b,path+'/'+str(i)) for i,(a,b) in enumerate(zip(old,new))),[])
    return [{'op':'replace','path':path,'value':new}]


FIELDS={'image','user','volumes','networks','environment','x-cstack-role'}
SELECTED={'uid','image','mounts','networks','env_names'}
KNOWN={'agent-a':'agent','agent-b':'agent','broker':'broker','receiver':'receiver','reviewer':'reviewer','approver':'approver'}
def apply_patch(document,operations):
    document=copy.deepcopy(document)
    for op in operations:
        parts=[x.replace('~1','/').replace('~0','~') for x in op['path'].split('/')[1:]]
        if not parts:
            if op['op']!='replace':raise ValueError('unsupported root patch')
            document=copy.deepcopy(op['value']);continue
        parent=document
        for part in parts[:-1]:parent=parent[int(part)] if isinstance(parent,list) else parent[part]
        key=int(parts[-1]) if isinstance(parent,list) else parts[-1]
        if op['op']=='remove':del parent[key]
        elif op['op']=='add' and isinstance(parent,list):parent.insert(key,copy.deepcopy(op['value']))
        elif op['op'] in {'add','replace'}:parent[key]=copy.deepcopy(op['value'])
        else:raise ValueError('unsupported patch operation')
    return document

def portable_observation_ir(ir,inputs):
    """Relocation changes only source labels for hash-identical known artifacts."""
    inputs=Path(inputs);root=Path(__file__).resolve().parents[1]
    files=[inputs/name for name in ('resolved.compose.json','resolved.runtime.json','host-observations.json')]+[root/'trusted_stack'/name for name in ('controller.py','outbox_receiver.py')]
    identities={(file.name,hashlib.sha256(file.read_bytes()).hexdigest()):file.name for file in files}
    for name in ('controller.py','outbox_receiver.py'):
        for generation in generations():
            vaulted=generation/'trusted_stack'/(name+'.pysrc')
            if vaulted.is_file():identities[(name,hashlib.sha256(vaulted.read_bytes()).hexdigest())]=name
    value=copy.deepcopy(ir)
    for provenance in value['sources']+[item['provenance'] for item in value['nodes']+value['edges']]:
        identity=(Path(provenance['source']).name,provenance['sha256'])
        if identity in identities:provenance['source']='pinned-artifact:'+identities[identity]
    return value

def build_plan(c,r,ir,base_sha256,host=None):
    original=copy.deepcopy(c);c=copy.deepcopy(c);claim=c.get('x-cstack',{});residual=[];actions=[]
    if not isinstance(c.get('services'),dict) or not c['services']:raise ValueError('services must be a nonempty object')
    policy=reference_policy()
    if not policy:raise ValueError('known reference principal policy unavailable')
    def issue(path,reason):residual.append({'path':path,'reason':reason})
    for name in list(c['services']):
        s=c['services'][name]
        if not isinstance(s,dict):raise ValueError('service must be an object')
        if s.get('x-cstack-role')=='deputy' and name not in KNOWN:
            del c['services'][name];continue
        if name in KNOWN:s['x-cstack-role']=KNOWN[name]
    agents=sorted(n for n,s in c['services'].items() if s.get('x-cstack-role')=='agent')
    for name,s in c['services'].items():
        role=s.get('x-cstack-role');p='/services/'+escape(name)
        if role=='agent' and name in agents[:2]:s['user']=str(policy['agent'][agents.index(name)])
        elif role in {'broker','receiver','reviewer','approver'}:s['user']=str(policy['admin' if role in {'broker','receiver'} else role][0])
        else:issue(p+'/x-cstack-role','role is outside the supported six-service profile')
        for key in list(s):
            if key not in FIELDS:
                if key=='read_only' and s[key] is True:issue(p+'/read_only','read_only rootfs is unsupported; retain this restriction until scanner support exists')
                else:del s[key]
        s['networks']=['isolated']
        if isinstance(s.get('environment'),dict):
            env=s['environment']
            for key in list(env):
                if key not in {'SLICE_ROLE','PYTHONPATH'}:del env[key]
            env['PYTHONPATH']='/slice'
            if role=='broker':env['SLICE_ROLE']='broker'
            elif env.get('SLICE_ROLE')=='broker':env['SLICE_ROLE']=name
        else:issue(p+'/environment','normalize environment to an explicit object before planning')
        expected={(claim.get('channel_source'),'/channel'):role not in {'broker','receiver'}}
        if role in {'broker','receiver'}:expected[(claim.get('database_source'),'/private')]=False
        if role=='receiver':expected[(claim.get('sink_source'),'/output')]=False
        out=[]
        for m in s.get('volumes',[]) if isinstance(s.get('volumes'),list) else []:
            if not isinstance(m,dict) or m.get('type')!='bind':continue
            pair=m.get('source'),m.get('target')
            if pair not in expected:continue
            m={k:v for k,v in m.items() if k in {'type','source','target','read_only','bind'}}
            if 'bind' in m and m['bind']!={'selinux':'z'}:m['bind']={'selinux':'z'}
            m['read_only']=expected[pair]
            if not any(v['target']==m['target'] for v in out):out.append(m)
        for (source,target),ro in expected.items():
            if role=='receiver' and target=='/channel':continue
            if source and not any(m['target']==target for m in out):out.append({'type':'bind','source':source,'target':target,'read_only':ro,'bind':{'selinux':'z'}})
        s['volumes']=out
    for key in list(c):
        if key not in {'services','networks','x-cstack'}:del c[key]
    c['networks']={'isolated':{'internal':True}}
    roles=[s.get('x-cstack-role') for s in c['services'].values()]
    if len(roles)!=6 or sorted(roles,key=str)!=['agent','agent','approver','broker','receiver','reviewer']:
        issue('/services','requires exactly two agents and one each broker, receiver, reviewer and approver; missing trusted services are not invented')
    root=Path(__file__).resolve().parents[1]
    for key,source in [('broker_sha256','controller.py'),('receiver_sha256','outbox_receiver.py')]:
        expected=hashlib.sha256((root/'trusted_stack'/source).read_bytes()).hexdigest()
        if claim.get(key)!=expected:issue('/x-cstack/'+key,'trusted source pin is missing or differs from reviewed code; inspect code and image correspondence before setting a pin, never infer it from the plan')
    # Preserve observations. A config patch cannot erase reported runtime authority.
    if isinstance(r,dict):
        for key in sorted(set(r)-{'services','capture'}):issue('/runtime/'+escape(key),'reported runtime fact remains outside supported capture; resolve and recapture it')
        for name,obs in r.get('services',{}).items():
            if name not in c['services']:issue('/runtime/services/'+escape(name),'remove/recreate the retired service and recollect; its recorded process is not erased by a patch')
            elif isinstance(obs,dict):
                for key in sorted(set(obs)-SELECTED):issue('/runtime/services/'+escape(name)+'/'+escape(key),'reported runtime authority remains outside selected inventory; resolve and recapture')
                service=c['services'][name]
                principal=service.get('user')
                numeric=int(principal) if isinstance(principal,str) and principal.isdigit() else None
                if numeric is None:issue('/services/'+escape(name)+'/user','numeric non-root UID must be reviewed for this unsupported role')
                proposed={'uid':numeric,'image':service.get('image'),'mounts':sorted([{k:v for k,v in m.items() if k!='bind'} for m in service['volumes']],key=lambda m:(m['source'],m['target'])),'networks':service['networks'],'env_names':sorted(service.get('environment',{}))}
                for key,value in proposed.items():
                    if obs.get(key)!=value:issue('/runtime/services/'+escape(name)+'/'+escape(key),'captured '+key+' differs from the proposed configuration; recreate/recollect before verification')

        for o in verify(ir)['obligations']:
            if o['premise'].startswith('runtime-snapshot:') and o['status'] in {'REFUTED','UNASSESSED'}:
                issue('/runtime/services/'+escape(o['premise'].split(':',1)[1]),'existing inventory '+o['detail']+'; recreate/recapture against the reviewed Compose')
    if host is None:
        issue('/observations','legacy snapshot has no fresh source realpaths, private-store custody or offline image observations; run a fresh scan')
    else:
        resolutions=host.get('resolutions',{})
        for key,service,mode in [('sink_source','receiver','0o700'),('database_source','broker','0o700'),('channel_source','broker','0o755')]:
            path=claim.get(key);fact=resolutions.get(path,{}) if isinstance(path,str) else {}
            principal=c['services'].get(service,{}).get('user')
            if not isinstance(principal,str) or not principal.isdigit() or int(principal)<=0:
                issue('/x-cstack/'+key,'missing trusted principal; no host ownership action is proposed')
                continue
            uid=int(principal)
            if fact.get('status')!='OBSERVED' or fact.get('type')!='directory':issue('/x-cstack/'+key,'declared directory has no valid host observation: '+str(path))
            elif any(fact.get('realpath','')==p or fact.get('realpath','').startswith(p.rstrip('/')+'/') or p.startswith(fact.get('realpath','').rstrip('/')+'/') for p in ('/etc','/proc','/sys','/dev','/var/lib/docker','/slice/trusted_stack','/slice/entry.py',str(Path(__file__).resolve().parents[1]/'trusted_stack'),str(Path(__file__).resolve().parents[1]/'extractors'),str(Path(__file__).resolve().parents[1]/'security_ir'))):
                issue('/x-cstack/'+key,'host system source is outside the supported profile; no ownership action is proposed')
            elif fact.get('uid')!=uid or (int(fact.get('mode','0'),8)!=0o755 if key=='channel_source' else int(fact.get('mode','0'),8)&0o077 or int(fact.get('mode','0'),8)&0o700!=0o700):
                action={'path':fact['realpath'],'uid':uid,'mode':mode,'cause':key+' custody differs from the supported profile'};actions.append(action)
                issue('/x-cstack/'+key,'host ownership/mode needs the separately reviewed host action; JSON Patch cannot fix it')
        for image,audit in host.get('images',{}).items():
            if audit.get('status')!='OBSERVED':issue('/images/'+escape(image),'offline image inspection UNKNOWN: '+audit.get('reason','unavailable'))
            elif audit.get('setid_paths'):issue('/images/'+escape(image),'setuid/setgid image entries remain; rebuild a supported image without them')
        for e in ir['edges']:
            if e['reachability']=='UNKNOWN':
                for reason in e['reason'].split('; '):
                    if any(x in reason for x in ('image-reference-source-correspondence','image-entrypoint-command-uninspected','image-principal-policy-evidence-mismatch')):
                        issue('/images/'+escape(e['from']),reason+'; config edits cannot establish baked-code correspondence')
    ops=patch_diff(original,c);assert apply_patch(original,ops)==c
    def redacted(document):
        d=copy.deepcopy(document)
        for service in d.get('services',{}).values():
            if isinstance(service.get('environment'),dict):
                for key in service['environment']:
                    if key not in {'SLICE_ROLE','PYTHONPATH'}:service['environment'][key]='<redacted>'
            elif isinstance(service.get('environment'),list):
                service['environment']=[entry if isinstance(entry,str) and entry.split('=',1)[0] in {'SLICE_ROLE','PYTHONPATH'} else '<redacted>' for entry in service['environment']]
        return d
    human=''.join(difflib.unified_diff(json.dumps(redacted(original),sort_keys=True,indent=2).splitlines(True),json.dumps(redacted(c),sort_keys=True,indent=2).splitlines(True),fromfile='declared.compose.json',tofile='proposed.compose.json'))
    unique={json.dumps(x,sort_keys=True):x for x in residual}
    return {'version':'0.1','base_sha256':base_sha256,'ir_sha256':verify(ir)['ir_sha256'],'patch':ops,'human_diff':human,'host_actions':actions,'residuals':[unique[k] for k in sorted(unique)],'next_step':'Apply to a copy, review host actions, recreate only a safe own deployment, recollect and run fresh scan + kernel verify. Input files and runtime facts were not changed.','scope':'Reference-profile proposal; no prospective CONDITIONAL verdict or runtime enforcement claim.'}
