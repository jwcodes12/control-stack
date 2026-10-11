"""Strict structural and consistency validator. Authorization is not reachability."""
import re

KINDS = {'DECLARED', 'STATIC_INFERRED', 'RUNTIME_OBSERVED', 'ENFORCED_TESTED', 'UNKNOWN'}
SHA = re.compile(r'[0-9a-f]{64}')
class InvalidIR(ValueError):
    pass

def require(ok, why):
    if not ok:
        raise InvalidIR(why)

def provenance(p):
    require(isinstance(p, dict) and set(p) == {'source', 'sha256', 'kind'}, 'missing/extra provenance data')
    require(isinstance(p['source'], str) and bool(p['source']), 'missing source path')
    require(isinstance(p['sha256'], str) and SHA.fullmatch(p['sha256']), 'invalid provenance hash')
    require(p['kind'] in KINDS, 'invalid provenance kind')

def validate(d):
    require(isinstance(d, dict) and set(d) == {'version','claim','sources','nodes','edges','snapshot'}, 'invalid IR fields')
    require(type(d['version']) is int and d['version'] == 0 and d['claim'] == 'local-file-two-agent-v0', 'unsupported IR version/claim')
    require(isinstance(d['sources'], list) and bool(d['sources']), 'missing sources')
    for p in d['sources']:
        provenance(p)
    require(len({p['source'] for p in d['sources']}) == len(d['sources']), 'duplicate/contradictory source pins')
    sources = {(p['source'], p['sha256']) for p in d['sources']}
    def prov(p):
        provenance(p)
        require((p['source'], p['sha256']) in sources, 'provenance not in pinned sources')
    require(isinstance(d['nodes'], list) and isinstance(d['edges'], list), 'nodes/edges must be lists')
    nodes = {}
    for n in d['nodes']:
        require(isinstance(n, dict) and set(n) == {'id','type','facts','provenance'}, 'missing/extra node fields')
        require(isinstance(n['id'], str) and n['id'] and n['id'] not in nodes, 'duplicate/empty node id')
        require(n['type'] in {'service','sink','database','unknown'}, 'invalid node type')
        prov(n['provenance'])
        require(isinstance(n['facts'], dict), 'facts must be object')
        if n['type'] == 'service':
            f = n['facts']
            require(set(f) == {'role','uid','image','privileged','host_network','env_names','runtime_match'}, 'missing service facts')
            require(f['role'] in {'agent','broker','receiver','reviewer','approver','deputy'}, 'invalid role')
            require(f['uid'] is None or type(f['uid']) is int and f['uid'] >= 0, 'invalid UID')
            require(isinstance(f['image'], str), 'invalid image')
            require(all(type(f[k]) is bool for k in ('privileged','host_network')), 'invalid privilege flags')
            require(f['runtime_match'] in {'MATCH','MISSING','DRIFT'}, 'invalid runtime match')
            require(isinstance(f['env_names'], list) and all(isinstance(x,str) for x in f['env_names']), 'env must contain names only')
        else:
            require(not n['facts'], 'resource facts must be empty')
        nodes[n['id']] = n
    require(set(nodes) >= {'sink','database','unknown'}, 'missing protected resources/unknown')
    require(nodes['sink']['type'] == 'sink' and nodes['database']['type'] == 'database' and nodes['unknown']['type'] == 'unknown', 'contradictory resource types')
    seen = {}
    for e in d['edges']:
        require(isinstance(e,dict) and set(e) == {'from','to','capability','reachability','authorization','provenance','reason'}, 'missing/extra edge fields')
        require(e['from'] in nodes and e['to'] in nodes, 'dangling edge')
        require(e['capability'] in {'write','read','call','escape','credential','opaque'}, 'invalid capability')
        require(e['reachability'] in {'PRESENT','ABSENT','UNKNOWN'}, 'invalid reachability')
        require(e['authorization'] in {'PERMITTED','FORBIDDEN','UNKNOWN'}, 'invalid authorization')
        prov(e['provenance'])
        require(isinstance(e['reason'],str) and bool(e['reason']), 'missing edge reason')
        require(e['provenance']['kind'] != 'UNKNOWN' or e['reachability'] == 'UNKNOWN', 'UNKNOWN evidence cannot deny/reify a path')
        require(e['reachability'] != 'ABSENT' or e['provenance']['kind'] in {'STATIC_INFERRED','ENFORCED_TESTED'}, 'absence needs explicit derivation/enforcement evidence')
        key = (e['from'], e['to'], e['capability'])
        require(key not in seen, 'duplicate/contradictory edge')
        seen[key] = e
    s = d['snapshot']
    require(isinstance(s,dict) and set(s) == {'compose_sha256','runtime_sha256','broker_sha256','receiver_sha256','budget','sink_source','database_source'}, 'missing snapshot fields')
    require(all(isinstance(s[k],str) and SHA.fullmatch(s[k]) for k in ('compose_sha256','runtime_sha256','broker_sha256','receiver_sha256')), 'invalid snapshot hashes')
    require(type(s['budget']) is int and s['budget'] > 0, 'positive shared budget required')
    require(all(isinstance(s[k], str) and s[k].startswith('/') for k in ('sink_source','database_source')), 'absolute protected source paths required')
    require(any(p['sha256'] == s['compose_sha256'] for p in d['sources']) and any(p['sha256'] == s['runtime_sha256'] for p in d['sources']), 'snapshot source hashes missing')
    require(all(any(p['sha256'] == s[k] for p in d['sources']) for k in ('broker_sha256','receiver_sha256')), 'trusted source hashes missing')
    return d
