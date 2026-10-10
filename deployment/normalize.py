"""Pinned Compose CLI normalization; no YAML parser or container launch."""
import copy
import json
import subprocess
from pathlib import Path
from extractors.compose import sha
PROJECT='cstack-r2-normalize'

def normalize(source,output,expected_sha256):
    source=Path(source).resolve();output=Path(output);output.mkdir(parents=True,exist_ok=True)
    if sha(source)!=expected_sha256:raise ValueError('Compose pin mismatch')
    argv=['docker','compose','-p',PROJECT,'-f',str(source),'config','--format','json']
    p=subprocess.run(argv,text=True,capture_output=True,timeout=30)
    if p.returncode:raise ValueError('Compose normalization failed: '+p.stderr)
    raw=json.loads(p.stdout);(output/'compose-cli.json').write_text(json.dumps(raw,sort_keys=True,indent=2)+'\n')
    try:original=json.loads(source.read_text())
    except json.JSONDecodeError:original={}
    c=canonical_profile(raw,original)
    canonical=output/'normalized.compose.json';canonical.write_text(json.dumps(c,sort_keys=True,separators=(',',':'))+'\n')
    version=subprocess.check_output(['docker','compose','version','--short'],text=True).strip()
    metadata={'source':str(source),'source_raw_sha256':sha(source),'normalizer':'docker compose config --format json','version':version,'argv':argv,'cli_output_sha256':sha(output/'compose-cli.json'),'canonical_output_sha256':sha(canonical),'role_binding':'explicit JSON x-cstack-role or YAML x-cstack.roles; no role inferred from environment or service name'}
    (output/'normalization.json').write_text(json.dumps(metadata,sort_keys=True,indent=2)+'\n')
    return canonical,metadata


def canonical_profile(raw,original=None):
    original=original or {}
    c=copy.deepcopy(raw);c.pop('name',None)
    roles=c.get('x-cstack',{}).pop('roles',{})
    if not isinstance(roles,dict):raise ValueError('x-cstack.roles must be a service-to-role mapping')
    if set(roles)-set(c.get('services',{})):raise ValueError('dangling explicit role binding')
    for name,service in c.get('services',{}).items():
        role=original.get('services',{}).get(name,{}).get('x-cstack-role')
        if role is not None and name in roles and role!=roles[name]:raise ValueError('conflicting explicit role bindings')
        service['x-cstack-role']=roles.get(name,role or 'deputy')
        for key in ('entrypoint','command'):
            if service.get(key,'not-present') is None:service.pop(key)
        networks=service.get('networks',{})
        if isinstance(networks,dict) and all(v in (None,{}) for v in networks.values()):service['networks']=sorted(networks)
        for mount in service.get('volumes',[]):
            if isinstance(mount,dict) and mount.get('type')=='bind':
                mount.setdefault('read_only',False)
                # This is creation policy, not mounted authority. Fresh scanning
                # checks that sources already exist; it never creates them.
                if isinstance(mount.get('bind'),dict):
                    mount['bind'].pop('create_host_path',None)
                    if not mount['bind']:mount.pop('bind')
    for name,network in c.get('networks',{}).items():
        if network.get('name')==PROJECT+'_'+name:network.pop('name')
        if network.get('ipam')=={}:network.pop('ipam')
    return c
