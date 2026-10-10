"""Collector for a deliberately restricted normalized Compose JSON profile.
JSON is a YAML subset. No Compose execution, interpolation, or secret values.
Unsupported features always add UNKNOWN authority edges.
"""
import hashlib
import json
import re
from pathlib import Path
from security_ir import validate

ROOT = Path(__file__).resolve().parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def collect(compose, runtime, expected_sha256):
    compose, runtime = Path(compose), Path(runtime)
    if sha(compose) != expected_sha256:
        raise ValueError('Compose pin mismatch')
    # JSON only prevents YAML tags/implicit values and interpolation surprises.
    c, r = json.loads(compose.read_text()), json.loads(runtime.read_text())
    sources = []
    def prov(path, kind):
        p = {'source':str(path), 'sha256':sha(path), 'kind':kind}
        if not any(x['source'] == p['source'] for x in sources):
            sources.append(dict(p))
        return p
    cp, rp = prov(compose,'DECLARED'), prov(runtime,'RUNTIME_OBSERVED')
    bp = prov(ROOT/'trusted_stack/controller.py','STATIC_INFERRED')
    op = prov(ROOT/'trusted_stack/outbox_receiver.py','STATIC_INFERRED')
    claim = c.get('x-cstack', {})
    sink = claim.get('sink_source', '/UNSPECIFIED-SINK')
    db = claim.get('database_source', '/UNSPECIFIED-DATABASE')
    channel = claim.get('channel_source', '/slice/channel')
    nodes = [{'id':k,'type':t,'facts':{},'provenance':cp} for k,t in [('sink','sink'),('database','database'),('unknown','unknown')]]
    edges = []
    def edge(src, dst, cap, reach, reason, p=cp):
        # Forbidden paths still contribute effective authority.
        for existing in edges:
            if (existing['from'],existing['to'],existing['capability']) == (src,dst,cap):
                existing['reason'] += '; '+reason
                if reach == 'UNKNOWN':
                    existing['reachability']='UNKNOWN'; existing['provenance']['kind']='UNKNOWN'
                return
        edges.append({'from':src,'to':dst,'capability':cap,'reachability':reach,
                      'authorization':'PERMITTED' if src in ('broker','receiver') or (dst == 'broker' and cap == 'call') else 'FORBIDDEN',
                      'provenance':dict(p, kind='UNKNOWN' if reach == 'UNKNOWN' else p['kind']), 'reason':reason})
    services = c.get('services',{})
    if not isinstance(services,dict) or not services:
        raise ValueError('services must be a nonempty object')
    def unknown(src, reason):
        # Merge unknown features into one edge, preserving all reasons.
        for e in edges:
            if e['from'] == src and e['to'] == 'unknown':
                e['reason'] += '; '+reason
                return
        edge(src,'unknown','opaque','UNKNOWN',reason)
    if set(c)-{'services','networks','x-cstack'} or set(claim)-{'sink_source','database_source','budget','broker_sha256','receiver_sha256','channel_source'}:
        unknown('unknown','unsupported top-level Compose/claim feature')
    def channel_sources(service, writable=False):
        mounts = service.get('volumes',[]) if isinstance(service,dict) else []
        if not isinstance(mounts,list): return set()
        return {v['source'] for v in mounts if isinstance(v,dict)
                and set(v)=={'type','source','target','read_only'}
                and v.get('type')=='bind' and v.get('target')=='/channel'
                and type(v.get('read_only')) is bool and (not writable or v['read_only'] is False)
                and isinstance(v.get('source'),str) and v['source'].startswith('/')
                and '$' not in v['source'] and '..' not in v['source'].split('/')}
    broker_channels = channel_sources(services.get('broker'),writable=True)
    for name, s in sorted(services.items()):
        if name in {'sink','database','unknown'} or not isinstance(s,dict):
            raise ValueError('invalid service')
        role = s.get('x-cstack-role','deputy')
        user = s.get('user','')
        uid = int(user) if isinstance(user,str) and re.fullmatch(r'[0-9]+',user) else None
        image = s.get('image','')
        env = s.get('environment',{})
        if not isinstance(env,dict):
            unknown(name,'unsupported environment syntax')
            env = {}
        for key in env:
            if key not in {'SLICE_ROLE','PYTHONPATH'} and not re.search(r'SINK|CREDENTIAL|TOKEN|SECRET|KEY|PASSWORD|PASS|PASSWD|AUTH|COOKIE|PRIVATE',key,re.I):
                unknown(name,'unlisted-environment: '+key)
        # Values intentionally neither serialized nor examined.
        facts = {'role':role,'uid':uid,'image':image,'privileged':s.get('privileged',False) is True,
                 'host_network':s.get('network_mode') == 'host','env_names':sorted(env),'runtime_match':'MISSING'}
        observed = r.get('services',{}).get(name)
        if observed is not None:
            keys = ('uid','image','mounts','networks','env_names')
            expected = {'uid':uid,'image':image,'mounts':sorted(s.get('volumes',[]),key=lambda v:(v.get('source',''),v.get('target',''))) if isinstance(s.get('volumes',[]),list) and all(isinstance(v,dict) for v in s.get('volumes',[])) else s.get('volumes',[]),'networks':s.get('networks',[]),'env_names':sorted(env)}
            facts['runtime_match'] = 'MATCH' if isinstance(observed,dict) and set(observed) == set(keys) and json.dumps(observed,sort_keys=True) == json.dumps(expected,sort_keys=True) else 'DRIFT'
        nodes.append({'id':name,'type':'service','facts':facts,'provenance':cp})
        if set(s)-{'image','user','volumes','networks','environment','privileged','network_mode','x-cstack-role'}:
            unknown(name,'unknown-feature: unsupported service feature: '+','.join(sorted(set(s)-{'image','user','volumes','networks','environment','privileged','network_mode','x-cstack-role'})))
        if 'privileged' in s and type(s['privileged']) is not bool:
            unknown(name,'unsupported privileged value')
        if 'network_mode' in s and s['network_mode'] != 'host':
            unknown(name,'unsupported network_mode')
        if uid is None or not re.fullmatch(r'(?:[^$]+@)?sha256:[0-9a-f]{64}', image) or any('$' in str(x) for x in (user,image)):
            unknown(name,'unresolved UID or unpinned/interpolated image')
        if facts['privileged'] or facts['host_network']:
            edge(name,'sink','escape','UNKNOWN','privileged-container' if facts['privileged'] else 'host-network')
        for key in env:
            if re.search(r'SINK|CREDENTIAL|TOKEN|SECRET|KEY|PASSWORD|PASS|PASSWD|AUTH|COOKIE|PRIVATE',key,re.I):
                edge(name,'sink','credential','UNKNOWN','opaque-credential-env-name:'+key)
        mounts = s.get('volumes',[])
        if not isinstance(mounts,list):
            unknown(name,'unsupported mounts')
            mounts = []
        for v in mounts:
            if not isinstance(v,dict) or set(v) != {'type','source','target','read_only'} or v.get('type') != 'bind' or type(v.get('read_only')) is not bool:
                unknown(name,'unsupported volume feature')
                continue
            source = v['source']
            if not isinstance(source,str) or not source.startswith('/') or '$' in source or '..' in source.split('/'):
                unknown(name,'unresolved mount source')
                continue
            target = v['target']
            # Exact bind allowlist, never a sensitive-path denylist. A path mounted
            # at another target is a different capability and remains unresolved.
            allowed = {(channel, '/channel')}
            if role in {'broker','receiver'}:
                allowed.add((db, '/private'))
            if role == 'receiver':
                allowed.add((sink, '/output'))
            if role not in {'agent','reviewer','approver','broker','receiver'}:
                allowed = set()
            # Ancestors AND descendants overlap; aliases/symlinks remain faithfulness premises.
            def overlaps(a,b):
                return a == b or a.startswith(b.rstrip('/')+'/') or b.startswith(a.rstrip('/')+'/')
            trusted_sources = ['/slice/trusted_stack', '/slice/entry.py', str(ROOT/'trusted_stack'), str(ROOT/'tools/deployment_container_entry.py'), str(ROOT/'extractors'), str(ROOT/'security_ir')]
            socket_paths=['/var/run/docker.sock','/run/docker.sock','/run/containerd/containerd.sock','/run/podman/podman.sock','/var/run/podman/podman.sock']
            runtime_socket = Path(source).name in {'docker.sock','containerd.sock','podman.sock'} or any(p.startswith(source.rstrip('/')+'/') for p in socket_paths)
            hazardous = (runtime_socket or Path(source).name in {'docker.sock','containerd.sock','podman.sock'}
                         or any(overlaps(source, x) for x in ['/proc','/sys','/dev','/etc','/var/lib/docker'])
                         or source == '/'
                         or any(x == source or x.startswith(source.rstrip('/')+'/') or source.startswith(x.rstrip('/')+'/') for x in trusted_sources))
            if hazardous:
                reason = ('runtime-socket-mount' if runtime_socket
                          else 'trusted-source-mount' if any(overlaps(source,x) for x in trusted_sources)
                          else 'host-control-mount')
                edge(name,'sink','escape','PRESENT',reason+': '+source)
            elif (source, target) not in allowed or (role in {'agent','reviewer','approver'} and not v['read_only']):
                unknown(name, 'unlisted-host-mount: '+source+' -> '+str(target))
            for resource, protected in [('sink',sink),('database',db)]:
                if overlaps(source,protected):
                    edge(name,resource,'read' if v['read_only'] else 'write','PRESENT','protected-'+resource+'-mount')
        if role == 'deputy':
            unknown(name,'uninspected deputy authority')
        if role in {'agent','reviewer','approver'}:
            shared = bool(channel_sources(s) & broker_channels)
            edge(name,'broker','call','PRESENT' if shared else 'UNKNOWN',
                 'shared-/channel-bind-to-broker' if shared else 'broker-channel-uninspected',
                 dict(cp,kind='STATIC_INFERRED'))
        if name not in ('broker','receiver') and observed is None:
            unknown(name,'runtime facts missing')
    if set(r)-{'services','capture'} or set(r.get('services',{}))-set(services):
        unknown('unknown','unsupported/extra runtime service')
    if 'capture' in r:
        capture = r['capture']
        if not isinstance(capture,dict) or set(capture) != {'kind','raw_sha256','independent_attestation'} or capture.get('kind') != 'docker-inspect' or capture.get('independent_attestation') is not False or not re.fullmatch(r'[0-9a-f]{64}', str(capture.get('raw_sha256',''))):
            unknown('unknown','unsupported runtime capture provenance')
    if c.get('networks') != {'isolated':{'internal':True}}:
        unknown('unknown','unsupported network topology')
    for name,s in sorted(services.items()):
        if s.get('networks',[]) != ['isolated']:
            unknown(name,'unsupported service networks')
    # Pin claims to the actual trusted source; drift is an unresolved path.
    if claim.get('broker_sha256') != bp['sha256'] or claim.get('receiver_sha256') != op['sha256']:
        unknown('unknown','trusted broker/receiver hash drift or missing pin')
    d = {'version':0,'claim':'local-file-two-agent-v0','sources':sources,'nodes':nodes,'edges':edges,
         'snapshot':{'compose_sha256':cp['sha256'],'runtime_sha256':rp['sha256'],'broker_sha256':bp['sha256'],
                     'receiver_sha256':op['sha256'],'budget':claim.get('budget',0),'sink_source':sink,'database_source':db}}
    return validate(d)
