"""Fresh v0.1 scan: normalize, observe mount realpaths and inspect local images.
Legacy collect() remains a parser/replayer of v0 snapshots, not a fresh host scan.
"""
import copy
import ast
import hashlib
import json
import subprocess
import stat
import tarfile
import tempfile
import uuid
from pathlib import Path
from deployment.normalize import normalize,canonical_profile
from deployment.pins import ENTRY,current_sources,known_generation,vaulted_file
from extractors.compose import collect,sha
from security_ir.validator import validate

def reference_policy(entry=None):
    tree=ast.parse((Path(entry) if entry else Path(__file__).resolve().parents[1]/'tools/deployment_container_entry.py').read_text())
    calls=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='execv']
    if len(calls)!=1 or len(calls[0].args)!=2 or not isinstance(calls[0].args[1],ast.List):return None
    values=calls[0].args[1].elts;result={}
    for flag,role,count in [('--agents','agent',2),('--reviewers','reviewer',1),('--approvers','approver',1),('--admins','admin',1)]:
        hits=[i for i,n in enumerate(values) if isinstance(n,ast.Constant) and n.value==flag]
        if len(hits)!=1 or hits[0]+1>=len(values):return None
        value=values[hits[0]+1]
        if not isinstance(value,ast.Constant) or not isinstance(value.value,str):return None
        try:uids=sorted(int(x) for x in value.value.split(','))
        except ValueError:return None
        if len(set(uids))!=count or any(x<=0 for x in uids):return None
        result[role]=uids
    return result

def delegation_enabled(entry=None):
    """True when the reference entry starts the broker with --allow-delegation (outside the R2 claim)."""
    tree=ast.parse((Path(entry) if entry else Path(__file__).resolve().parents[1]/'tools/deployment_container_entry.py').read_text())
    return any(isinstance(n,ast.Constant) and n.value=='--allow-delegation' for n in ast.walk(tree))

def inspect_image(image):
    try:
        p=subprocess.run(['docker','image','inspect',image],capture_output=True,text=True,timeout=10)
        if p.returncode:return {'status':'UNKNOWN','reason':'local image unavailable'}
        row=json.loads(p.stdout)[0];config=row['Config']
        if config.get('Volumes'):return {'status':'UNKNOWN','reason':'image-declared volumes not supported'}
        name='cstack-r2-image-audit-'+uuid.uuid4().hex[:12]
        created_id=None
        try:
            created=subprocess.run(['docker','create','--name',name,'--network','none','--user','23705','--entrypoint','/usr/bin/true',image],capture_output=True,text=True,timeout=10)
            if created.returncode:return {'status':'UNKNOWN','reason':'offline image export unavailable'}
            created_id=created.stdout.strip()
            with tempfile.TemporaryDirectory(prefix='cstack-r2-image-audit-',dir=Path(__file__).resolve().parents[1]/'.git') as tmp:
                archive=Path(tmp)/'rootfs.tar'
                with archive.open('wb') as f:
                    exported=subprocess.run(['docker','export',name],stdout=f,stderr=subprocess.PIPE,timeout=30)
                if exported.returncode:return {'status':'UNKNOWN','reason':'offline image export failed'}
                with tarfile.open(archive) as tar:
                    members=tar.getmembers()
                    inventory=sorted((m.name,m.mode,m.uid,m.gid,m.type.decode('ascii')) for m in members)
                    wanted={'slice/entry.py',*[('slice/trusted_stack/'+f.name) for f in (Path(__file__).resolve().parents[1]/'trusted_stack').glob('*.py')]}
                    sources={m.name.removeprefix('./'):hashlib.sha256(tar.extractfile(m).read()).hexdigest() for m in members if m.isfile() and m.name.removeprefix('./') in wanted}
                setid=[name for name,mode,*_ in inventory if mode&0o6000]
                return {'status':'OBSERVED','image':row['Id'],'image_user':config.get('User',''),'entrypoint':config.get('Entrypoint'),'command':config.get('Cmd'),'setid_paths':setid,'export_sha256':sha(archive),'source_sha256':sources,'mode_inventory_sha256':hashlib.sha256(json.dumps(inventory,separators=(',',':')).encode()).hexdigest(),'principal_policy':reference_policy(),'inspection':'stopped create with network none, numeric UID 23705, harmless overridden entrypoint; export; rm; never start','basis':'Docker inspect/export; daemon observations, not attestation'}
        finally:
            if created_id:subprocess.run(['docker','rm',created_id],capture_output=True,timeout=10)
    except (OSError,ValueError,subprocess.SubprocessError,tarfile.TarError):return {'status':'UNKNOWN','reason':'offline image inspection unavailable'}

def scan(compose,runtime,expected_sha256,output,image_observer=inspect_image,observed_snapshot=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    if observed_snapshot is None:cp,metadata=normalize(compose,output,expected_sha256)
    else:
        if sha(compose)!=expected_sha256:raise ValueError('Compose pin mismatch')
        cp=output/'normalized.compose.json'
        try:input_json=json.loads(Path(compose).read_text())
        except json.JSONDecodeError:input_json={}
        assert canonical_profile(json.loads((output/'compose-cli.json').read_text()),input_json)==json.loads(cp.read_text())
        metadata=json.loads((output/'normalization.json').read_text())
        assert metadata['source_raw_sha256']==sha(compose) and metadata['cli_output_sha256']==sha(output/'compose-cli.json') and metadata['canonical_output_sha256']==sha(cp)
    original=json.loads(cp.read_text());c=copy.deepcopy(original);r=json.loads(Path(runtime).read_text())
    resolutions=copy.deepcopy(observed_snapshot['resolutions']) if observed_snapshot is not None else {};issues={};images=copy.deepcopy(observed_snapshot['images']) if observed_snapshot is not None else {}
    def resolve(source):
        if not isinstance(source,str) or not source.startswith('/') or '$' in source:return None
        if source not in resolutions:
            if observed_snapshot is not None:return None
            try:
                resolved=Path(source).resolve(strict=True);st=resolved.stat()
                resolutions[source]={'status':'OBSERVED','realpath':str(resolved),'uid':st.st_uid,'mode':oct(st.st_mode&0o7777),'device':st.st_dev,'inode':st.st_ino,'type':'directory' if stat.S_ISDIR(st.st_mode) else 'other'}
            except (OSError,RuntimeError):resolutions[source]={'status':'UNKNOWN','reason':'mount source cannot be resolved'}
        return resolutions[source].get('realpath')
    for key in ('sink_source','database_source','channel_source'):
        path=c.get('x-cstack',{}).get(key);real=resolve(path)
        if real:c['x-cstack'][key]=real
    for name,s in c['services'].items():
        issues[name]=[]
        for m in s.get('volumes',[]):
            if isinstance(m,dict) and m.get('type')=='bind':
                real=resolve(m.get('source'))
                if real:m['source']=real
                else:issues[name].append('unresolved-mount-source')
        observed=r.get('services',{}).get(name,{})
        mounts=observed.get('mounts',[]) if isinstance(observed,dict) else []
        for m in mounts if isinstance(mounts,list) else []:
            if isinstance(m,dict) and m.get('type')=='bind':
                real=resolve(m.get('source'))
                if real:m['source']=real
                else:issues[name].append('unresolved-runtime-mount-source')
        if isinstance(mounts,list) and all(isinstance(m,dict) and isinstance(m.get('source'),str) and isinstance(m.get('target'),str) for m in mounts):mounts.sort(key=lambda m:(m['source'],m['target']))
        image=s.get('image','')
        if image not in images:images[image]=image_observer(image)
        audit=images[image]
        if audit['status']=='UNKNOWN':issues[name].append('image-inspection-UNKNOWN: '+audit['reason'])
        else:
            if audit['setid_paths']:issues[name].append('image-setuid-setgid-binaries')
            if audit['entrypoint']!=['/usr/bin/python3','/slice/entry.py'] or audit['command']:issues[name].append('image-entrypoint-command-uninspected')
            expected_sources=current_sources();policy_entry=None
            if observed_snapshot is not None and audit.get('source_sha256')!=expected_sources and known_generation(audit.get('source_sha256')):
                # Replay of archived evidence: the image carried an earlier vaulted generation, so compare against that
                # generation (and read its entry's policy). A fresh scan never takes this branch.
                expected_sources=audit['source_sha256'];policy_entry=vaulted_file(ENTRY,expected_sources['slice/entry.py'])
            if audit.get('source_sha256')!=expected_sources:issues[name].append('image-reference-source-correspondence-UNKNOWN')
            if not isinstance(s.get('user'),str) or not s['user'].isdecimal():issues[name].append('image-USER-not-explicitly-overridden')
            policy=reference_policy(policy_entry) if audit.get('source_sha256')==expected_sources else None
            if policy is not None and delegation_enabled(policy_entry):issues[name].append('broker-delegation-enabled-outside-claim-UNKNOWN')
            if 'principal_policy' in audit and audit['principal_policy']!=policy:issues[name].append('image-principal-policy-evidence-mismatch-UNKNOWN')
            role=s.get('x-cstack-role');policy_role='admin' if role in {'broker','receiver'} else role
            if not isinstance(policy,dict) or not isinstance(s.get('user'),str) or not s['user'].isdecimal() or int(s['user']) not in policy.get(policy_role,[]):issues[name].append('image-principal-policy-mismatch-UNKNOWN')
            env=s.get('environment',{})
            if env.get('PYTHONPATH')!='/slice' or (env.get('SLICE_ROLE')=='broker')!=(role=='broker'):issues[name].append('reference-entry-environment-mismatch-UNKNOWN')
    for key,service in [('sink_source','receiver'),('database_source','broker')]:
        path=original.get('x-cstack',{}).get(key)
        fact=resolutions.get(path,{}) if isinstance(path,str) else {}
        uid=c['services'].get(service,{}).get('user','')
        if fact.get('status')!='OBSERVED' or not uid.isdecimal() or fact.get('uid')!=int(uid) or fact.get('type')!='directory' or int(fact.get('mode','0'),8)&0o077 or int(fact.get('mode','0'),8)&0o700!=0o700:
            if service in issues:issues[service].append('private-store-custody-UNKNOWN')
    channel=original.get('x-cstack',{}).get('channel_source')
    fact=resolutions.get(channel,{}) if isinstance(channel,str) else {}
    uid=c['services'].get('broker',{}).get('user','')
    if fact.get('type')!='directory' or not uid.isdecimal() or fact.get('uid')!=int(uid) or int(fact.get('mode','0'),8)!=0o755:
        if 'broker' in issues:issues['broker'].append('channel-custody-access-UNKNOWN')
    # Derived canonical snapshots are the IR provenance. Original byte pins and
    # CLI version/output are retained separately, so whitespace cannot change IR.
    cp=output/'resolved.compose.json';rp=output/'resolved.runtime.json'
    if observed_snapshot is None:
        cp.write_text(json.dumps(c,sort_keys=True,separators=(',',':'))+'\n');rp.write_text(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n')
    else:assert json.loads(cp.read_text())==c and json.loads(rp.read_text())==r
    raw_exports={image:audit.pop('export_sha256') for image,audit in images.items() if 'export_sha256' in audit}
    if observed_snapshot is None:(output/'image-export-capture.json').write_text(json.dumps(raw_exports,sort_keys=True,indent=2)+'\n')
    facts={'resolutions':resolutions,'images':images}
    facts_path=output/'host-observations.json'
    if observed_snapshot is None:facts_path.write_text(json.dumps(facts,sort_keys=True,separators=(',',':'))+'\n')
    else:assert json.loads(facts_path.read_text())==facts
    ir=collect(cp,rp,sha(cp),replay=observed_snapshot is not None);ir['version']='0.1'
    provenance={'source':str(facts_path),'sha256':sha(facts_path),'kind':'RUNTIME_OBSERVED'};ir['sources'].append(provenance)
    for service,reasons in issues.items():
        if reasons:
            existing=next((e for e in ir['edges'] if e['from']==service and e['to']=='unknown' and e['capability']=='opaque'),None)
            reason='; '.join(sorted(set(reasons)))
            if existing:existing['reason']+='; '+reason;existing['reachability']='UNKNOWN';existing['provenance']=dict(provenance,kind='UNKNOWN')
            else:ir['edges'].append({'from':service,'to':'unknown','capability':'opaque','reachability':'UNKNOWN','authorization':'UNKNOWN','provenance':dict(provenance,kind='UNKNOWN'),'reason':reason})
    ir['edges'].sort(key=lambda e:(e['from'],e['to'],e['capability']))
    return validate(ir)


def replay_snapshot(compose,runtime,output):
    """Reconstruct an archived observation; this is not a fresh host assessment."""
    output=Path(output);facts=json.loads((output/'host-observations.json').read_text())
    def no_new_observation(image):raise AssertionError('archived image observation missing')
    return scan(compose,runtime,sha(compose),output,no_new_observation,facts)
