#!/usr/bin/env python3
"""Read-only Docker-daemon inventory, not independent attestation.
Raw inspect is retained by hash. Unexpected selected runtime security settings
make the normalized inventory drift rather than quietly being dropped.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

def capture(compose, project, output):
    c=json.loads(Path(compose).read_text()); output=Path(output); output.mkdir(parents=True,exist_ok=True)
    ids=subprocess.check_output(['docker','compose','-p',project,'-f',str(compose),'ps','-q'],text=True).split()
    if not ids: raise ValueError('no running containers to inspect')
    raw=subprocess.check_output(['docker','inspect',*ids])
    (output/'docker-inspect.raw.json').write_bytes(raw)
    services=normalize(c,json.loads(raw),project)
    result={'capture':{'kind':'docker-inspect','raw_sha256':hashlib.sha256(raw).hexdigest(),'independent_attestation':False},'services':services}
    (output/'runtime.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    return result
def normalize(c, rows, project):
    services={}
    for row in rows:
        name=row['Config']['Labels']['com.docker.compose.service']
        if name in services: raise ValueError('duplicate runtime service')
        uid=row['Config']['User']
        mounts=[{'type':m['Type'],'source':m['Source'],'target':m['Destination'],'read_only':not m['RW']} for m in row['Mounts']]
        # Compose order is not authority: deterministic ordering matches declarations.
        mounts.sort(key=lambda m:(m['source'],m['target']))
        declared=c['services'].get(name,{})
        # Identity/image come from observed Config and resolved image ID, not Compose.
        observed={'uid':int(uid) if uid.isdecimal() else None,'image':row['Image'],'mounts':mounts,
                  'networks':sorted(n.removeprefix(project+'_') for n in row['NetworkSettings']['Networks']),
                  'env_names':sorted(e.split('=',1)[0] for e in row['Config']['Env'])}
        hc=row['HostConfig']
        if hc['Privileged'] or hc.get('CapAdd') or hc.get('Devices') or hc.get('PidMode') or hc.get('IpcMode') not in ('private','') or hc.get('UsernsMode') != '' or hc.get('SecurityOpt') or hc.get('NetworkMode')=='host' or any(hc.get(k) for k in ('GroupAdd','VolumesFrom','Tmpfs','ExtraHosts','PortBindings','Sysctls','DeviceRequests')) or row['Config'].get('Entrypoint') != ['/usr/bin/python3','/slice/entry.py'] or row['Config'].get('Cmd'):
            observed['unsupported_runtime_security']='nondefault namespace/capability/device/security policy'
        services[name]=observed
    return services

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('compose');ap.add_argument('--project',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();capture(a.compose,a.project,a.output)
