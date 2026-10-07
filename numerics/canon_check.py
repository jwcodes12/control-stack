"""Python mirror of ledger/CANON.lean (desugar, Stmt.append, flatten, rename, occ, firstOcc, locals,
canonMap, canon) + a fuel interpreter mirroring Exec.  Checks on random programs:
 (i)   semantics: out(canon p) == out(p) on several inputs
 (ii<) canon invariant under random generator steps: for->while at a random position, ;-reassociation at a
       random position, random admissible renaming
 (ii>) p ~ canon p is witnessed constructively (not checked here); canon(canon p) == canon p (idempotence)
 control: an inadmissible renaming (moving a parameter) changes outputs."""
import random
rng = random.Random(17)
# AST as tuples: ('lit',n) ('var',v) ('add',a,b) ('sub',a,b) ('mul',a,b); BExp ('lt',a,b) ('eq',a,b) ('not',b) ('and',b,c)
# Stmt ('skip',) ('assign',v,a) ('seq',s,t) ('ite',b,s,t) ('while',b,s) ('cfor',i,c,st,body)
def aev(a, s):
    k = a[0]
    if k == 'lit': return a[1]
    if k == 'var': return s.get(a[1], 0)
    x, y = aev(a[1], s), aev(a[2], s)
    return x + y if k == 'add' else x - y if k == 'sub' else x * y
def bev(b, s):
    k = b[0]
    if k == 'lt': return aev(b[1], s) < aev(b[2], s)
    if k == 'eq': return aev(b[1], s) == aev(b[2], s)
    if k == 'not': return not bev(b[1], s)
    return bev(b[1], s) and bev(b[2], s)
class OutOfFuel(Exception): pass
def run(st, s, fuel):
    if fuel[0] <= 0: raise OutOfFuel
    fuel[0] -= 1
    k = st[0]
    if k == 'skip': return s
    if k == 'assign': s = dict(s); s[st[1]] = aev(st[2], s); return s
    if k == 'seq': return run(st[2], run(st[1], s, fuel), fuel)
    if k == 'ite': return run(st[2] if bev(st[1], s) else st[3], s, fuel)
    if k == 'while':
        while bev(st[1], s): s = run(st[2], s, fuel)
        return s
    if k == 'cfor': return run(('seq', st[1], ('while', st[2], ('seq', st[4], st[3]))), s, fuel)
def out(p, ins):
    k, body, ret = p
    s = {v: (ins[v] if v < len(ins) else 0) for v in range(k)}
    try: return aev(ret, run(body, s, [5000]))
    except OutOfFuel: return None
def desugar(st):
    k = st[0]
    if k in ('skip', 'assign'): return st
    if k == 'seq': return ('seq', desugar(st[1]), desugar(st[2]))
    if k == 'ite': return ('ite', st[1], desugar(st[2]), desugar(st[3]))
    if k == 'while': return ('while', st[1], desugar(st[2]))
    return ('seq', desugar(st[1]), ('while', st[2], ('seq', desugar(st[4]), desugar(st[3]))))
def append(s, t):
    return ('seq', s[1], append(s[2], t)) if s[0] == 'seq' else ('seq', s, t)
def flatten(st):
    k = st[0]
    if k in ('skip', 'assign'): return st
    if k == 'seq': return append(flatten(st[1]), flatten(st[2]))
    if k == 'ite': return ('ite', st[1], flatten(st[2]), flatten(st[3]))
    if k == 'while': return ('while', st[1], flatten(st[2]))
    return ('cfor', flatten(st[1]), st[2], flatten(st[3]), flatten(st[4]))
def arn(f, a):
    if a[0] == 'lit': return a
    if a[0] == 'var': return ('var', f(a[1]))
    return (a[0], arn(f, a[1]), arn(f, a[2]))
def brn(f, b):
    if b[0] == 'not': return ('not', brn(f, b[1]))
    if b[0] == 'and': return ('and', brn(f, b[1]), brn(f, b[2]))
    return (b[0], arn(f, b[1]), arn(f, b[2]))
def srn(f, st):
    k = st[0]
    if k == 'skip': return st
    if k == 'assign': return ('assign', f(st[1]), arn(f, st[2]))
    if k == 'seq': return ('seq', srn(f, st[1]), srn(f, st[2]))
    if k == 'ite': return ('ite', brn(f, st[1]), srn(f, st[2]), srn(f, st[3]))
    if k == 'while': return ('while', brn(f, st[1]), srn(f, st[2]))
    return ('cfor', srn(f, st[1]), brn(f, st[2]), srn(f, st[3]), srn(f, st[4]))
def prn(f, p): return (p[0], srn(f, p[1]), arn(f, p[2]))
def aocc(a):
    if a[0] == 'lit': return []
    if a[0] == 'var': return [a[1]]
    return aocc(a[1]) + aocc(a[2])
def bocc(b):
    if b[0] == 'not': return bocc(b[1])
    if b[0] == 'and': return bocc(b[1]) + bocc(b[2])
    return aocc(b[1]) + aocc(b[2])
def socc(st):
    k = st[0]
    if k == 'skip': return []
    if k == 'assign': return [st[1]] + aocc(st[2])
    if k == 'seq': return socc(st[1]) + socc(st[2])
    if k == 'ite': return bocc(st[1]) + socc(st[2]) + socc(st[3])
    if k == 'while': return bocc(st[1]) + socc(st[2])
    return socc(st[1]) + bocc(st[2]) + socc(st[3]) + socc(st[4])
def pocc(p): return socc(p[1]) + aocc(p[2])
def firstOcc(l):
    acc = []
    for v in l:
        if v not in acc: acc.append(v)
    return acc
def canon(p):
    d = (p[0], flatten(desugar(p[1])), p[2])
    loc = [v for v in firstOcc(pocc(d)) if d[0] <= v]
    cm = lambda v: v if v < d[0] else d[0] + (loc.index(v) if v in loc else len(loc))
    return prn(cm, d)
def gA(d):
    if d == 0 or rng.random() < 0.4:
        return ('lit', rng.randint(0, 2)) if rng.random() < 0.4 else ('var', rng.randint(0, 5))
    return (rng.choice(['add', 'sub']), gA(d - 1), gA(d - 1))
def gS(d):
    r = rng.random()
    if d == 0 or r < 0.25: return ('assign', rng.randint(0, 5), gA(2))
    if r < 0.5: return ('seq', gS(d - 1), gS(d - 1))
    if r < 0.65: return ('ite', ('lt', gA(1), gA(1)), gS(d - 1), gS(d - 1))
    v = rng.randint(2, 5)
    if r < 0.85: return ('cfor', ('assign', v, ('lit', 0)), ('lt', ('var', v), ('lit', 3)), ('assign', v, ('add', ('var', v), ('lit', 1))), gS(d - 1))
    return ('seq', ('assign', v, ('lit', 0)), ('while', ('lt', ('var', v), ('lit', 2)), ('seq', gS(d - 1), ('assign', v, ('add', ('var', v), ('lit', 1))))))
def positions(st, path=()):
    yield path, st
    k = st[0]
    kids = {'seq': (1, 2), 'ite': (2, 3), 'while': (2,), 'cfor': (1, 3, 4)}.get(k, ())
    for i in kids: yield from positions(st[i], path + (i,))
def replace(st, path, new):
    if not path: return new
    l = list(st); l[path[0]] = replace(st[path[0]], path[1:], new); return tuple(l)
def random_step(p):
    k, body, ret = p
    cands = [(pa, s) for pa, s in positions(body) if s[0] == 'cfor' or (s[0] == 'seq' and s[1][0] == 'seq')]
    if cands and rng.random() < 0.7:
        pa, s = rng.choice(cands)
        if s[0] == 'cfor': new = ('seq', s[1], ('while', s[2], ('seq', s[4], s[3])))
        else: new = ('seq', s[1][1], ('seq', s[1][2], s[2]))
        return (k, replace(body, pa, new), ret)
    vs = sorted(set(pocc(p)))
    locs = [v for v in vs if v >= k]
    targets = rng.sample(range(k, k + 40), len(locs))
    mp = dict(zip(locs, targets))
    return prn(lambda v: mp.get(v, v), p)
bad = {"sem": 0, "inv": 0, "idem": 0}; ctrl = 0; tested = 0
for trial in range(3000):
    k = rng.randint(0, 2)
    p = (k, gS(4), ('add', ('var', rng.randint(0, 5)), ('var', rng.randint(0, 5))))
    ins_list = [[rng.randint(-2, 3) for _ in range(k)] for _ in range(3)]
    o = [out(p, ins) for ins in ins_list]
    if None in o: continue
    tested += 1
    if [out(canon(p), ins) for ins in ins_list] != o: bad["sem"] += 1
    q = p
    for _ in range(rng.randint(1, 6)): q = random_step(q)
    if canon(q) != canon(p): bad["inv"] += 1
    if canon(canon(p)) != canon(p): bad["idem"] += 1
    if k >= 1 and [out(prn(lambda v: v + 1, p), ins) for ins in ins_list] != o: ctrl += 1
print(f"{tested} terminating random programs: failures {bad}; control (parameter shift changes output) fired {ctrl} times")
