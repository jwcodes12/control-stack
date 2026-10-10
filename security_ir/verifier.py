"""Obligation bundle for the local-file slice. No ASSURED verdict exists in v0."""
import json
from pathlib import Path
from .validator import validate

def verify(ir):
    validate(ir)
    services = {n['id']:n['facts'] for n in ir['nodes'] if n['type']=='service'}
    obligations = []
    def add(name,status,detail):
        obligations.append({'premise':name,'status':status,'detail':detail})
    agents = [k for k,v in services.items() if v['role']=='agent']
    role_ok = len(agents)==2 and services.get('broker',{}).get('role')=='broker' and services.get('receiver',{}).get('role')=='receiver' and sum(v['role']=='broker' for v in services.values())==1 and sum(v['role']=='receiver' for v in services.values())==1 and sum(v['role']=='reviewer' for v in services.values())==1 and sum(v['role']=='approver' for v in services.values())==1
    add('supported-roles','CONDITIONAL' if role_ok else 'REFUTED','two agents, one named broker and one named receiver required')
    trusted = [k for k,v in services.items() if v['role'] in {'broker','receiver','reviewer','approver'}]
    uids = [services[k]['uid'] for k in agents+trusted]
    uid_ok = bool(trusted) and all(x is not None and x>0 for x in uids) and len({services[k]['uid'] for k in agents})==2 and all(services[a]['uid'] != services[t]['uid'] for a in agents for t in trusted) and services.get('broker',{}).get('uid')==services.get('receiver',{}).get('uid') and all(services[k]['uid']!=services.get('broker',{}).get('uid') for k in services if k not in {'broker','receiver'})
    uid_ok = uid_ok and len({services[k]['uid'] for k in trusted if k != 'receiver'}) == len([k for k in trusted if k != 'receiver'])
    add('identity-separation','UNASSESSED' if any(x is None for x in uids) else 'CONDITIONAL' if uid_ok else 'REFUTED','distinct agent/trusted UIDs; only broker/receiver share trusted owner; trusted-role-uid-collision on failure')
    for name,f in services.items():
        add('runtime-snapshot:'+name, {'MATCH':'CONDITIONAL','MISSING':'UNASSESSED','DRIFT':'REFUTED'}[f['runtime_match']], f['runtime_match'])
        if f['privileged'] or f['host_network']:
            add('isolation:'+name,'REFUTED','privileged-container' if f['privileged'] else 'host-network')
    for e in ir['edges']:
        if e['reachability']=='UNKNOWN':
            add('unknown:'+e['from']+':'+e['to'],'UNASSESSED',e['reason'])
        elif e['reachability']=='PRESENT':
            if e['to']=='sink' and not (e['from']=='receiver' and e['capability']=='write'):
                add('sink-authority:'+e['from'],'REFUTED', ('alternate-deputy-sink-credentials' if services.get(e['from'],{}).get('role')=='deputy' else 'writable-sink-mount' if e['capability']=='write' else 'unprotected-sink-access')+': '+e['reason'])
            if e['to']=='database' and e['from'] not in {'broker','receiver'}:
                add('database-custody:'+e['from'],'REFUTED','agent-broker-db-access: '+e['reason'])
    writers = [e['from'] for e in ir['edges'] if e['to']=='sink' and e['capability']=='write' and e['reachability']=='PRESENT']
    dbwriters = [e['from'] for e in ir['edges'] if e['to']=='database' and e['capability']=='write' and e['reachability']=='PRESENT']
    add('useful-sink-path','CONDITIONAL' if writers==['receiver'] else 'REFUTED','exactly the receiver has the writable sink mount')
    add('shared-database','CONDITIONAL' if sorted(dbwriters)==['broker','receiver'] else 'REFUTED','broker and receiver must use the same pinned database')
    # Graph reachability ignores policy labels and walks every present path,
    # removing the two trusted mediation components; unknown edges are unresolved above.
    for a in agents:
        seen, pending = {a}, [a]
        while pending:
            src = pending.pop()
            for e in ir['edges']:
                if e['from']==src and e['reachability']=='PRESENT' and e['to'] not in {'broker','receiver'} and e['to'] not in seen:
                    seen.add(e['to']); pending.append(e['to'])
        if seen & {'sink','database'}:
            add('exclusive-path:'+a,'REFUTED','bypass path reaches '+','.join(sorted(seen & {'sink','database'})))
    add('IR-faithfulness','CONDITIONAL','snapshot exhausts scoped effective authority and faithfully abstracts trusted protocol, Linux identity/confinement, storage and sink publication; not proved')
    add('Lean-contract-instances','UNASSESSED','run tools/check_deployment_lean.py against this exact IR to kernel-check facts and contracts; source names alone are not proof')
    return {'version':0,'claim':ir['claim'],'snapshot':ir['snapshot'],'ir_sha256':__import__('hashlib').sha256(json.dumps(ir,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
            'verdict':'UNASSURED' if any(o['status'] in {'REFUTED','UNASSESSED'} and o['premise']!='Lean-contract-instances' for o in obligations) else 'CONDITIONAL',
            'obligations':obligations,
            'scope':'configuration/model candidate; CONDITIONAL always retains faithfulness and pending kernel checks; no deployment-assured result'}

def report(bundle):
    if bundle.get('version') != 0 or bundle.get('verdict') not in {'CONDITIONAL','UNASSURED'}:
        raise ValueError('invalid obligation bundle')
    lines = ['# Local file deployment slice', '', '**'+bundle['verdict']+'**', '', bundle['scope'], '', '| Premise | Status | Evidence / limitation |','|---|---|---|']
    for o in bundle['obligations']:
        lines.append('| '+o['premise'].replace('|','\\|')+' | '+o['status']+' | '+o['detail'].replace('|','\\|').replace('\n',' ')+' |')
    lines += ['', 'Result lifetime: invalidated by changed mounts, UIDs, credentials, networks, image digests, trusted source hashes, policy/budget, or runtime inventory.']
    return '\n'.join(lines)+'\n'
