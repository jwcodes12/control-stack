"""UMCERT brute-force checks (exact Fractions, mirroring Lean semantics).
(R)  one-shot reduction: per-seed protocol risk <= one-shot value at the worst bad x for that seed's rule
(G0) survH antitone in h for every schedule kappa in [0,1]
(W)  grid certificate for m=12, s_c=1, r=1 (stratified) and the bracket"""
from fractions import Fraction as F
from math import comb
import random, itertools, sys
random.seed(1)

def survH(h, kap, n, j):
    # memo on (n,j)
    memo = {}
    def S(n, j):
        if n == 0: return F(1)
        if (n, j) in memo: return memo[(n, j)]
        v = (1 - h) * S(n - 1, j) + h * (1 - kap(j)) * S(n - 1, j + 1)
        memo[(n, j)] = v
        return v
    return S(n, j)

def binCDF(n, s, h):
    return sum(F(comb(n, j)) * h**j * (1 - h)**(n - j) for j in range(s + 1) if j <= n)

def capB(r, b, a):
    return 1 - r + r * a if b > 0 else a

# ---- (G0) antitone
viol = 0
for trial in range(400):
    kv = [F(random.randint(0, 4), 4) for _ in range(12)]
    kap = lambda j, kv=kv: kv[j] if j < len(kv) else F(1)
    n = random.randint(0, 7); j = random.randint(0, 3)
    hs = sorted(F(random.randint(0, 10), 10) for _ in range(2))
    if survH(hs[1], kap, n, j) > survH(hs[0], kap, n, j): viol += 1
print("G0 antitone violations:", viol)

# ---- (R) per-seed reduction on random instances of the halting protocol
def cat(Bad, M, phi, pi, r, b, n, u, hist):
    if n == 0: return F(0)
    tot = F(0)
    X = range(len(M)); Z = range(len(M[0]))
    for x in X:
        px = pi(hist, x)
        if px == 0: continue
        s = F(0)
        for z in Z:
            if M[x][z] == 0: continue
            pas = phi[z] * (1 if Bad[x] else cat(Bad, M, phi, pi, r, b, n - 1, u, hist + ((x, z, True),)))
            if u < b:
                fl = (1 - phi[z]) * ((1 - r) if Bad[x] else cat(Bad, M, phi, pi, r, b, n - 1, u + 1, hist + ((x, z, False),)))
            else:
                fl = 0
            s += M[x][z] * (pas + fl)
        tot += px * s
    return tot

def rnddist(k):
    w = [random.randint(0, 3) for _ in range(k)]
    if sum(w) == 0: w[random.randrange(k)] = 1
    return [F(a, sum(w)) for a in w]

viol = 0; worst = F(0)
for trial in range(300):
    nX, nZ = random.randint(2, 3), random.randint(2, 3)
    Bad = [random.random() < 0.5 for _ in range(nX)]
    M = [rnddist(nZ) for _ in range(nX)]
    PH = rnddist(nX)
    push = [sum(PH[x] * M[x][z] for x in range(nX)) for z in range(nZ)]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    tbl = {}
    def pi(hist, x, tbl=tbl, nX=nX):
        key = hist
        if key not in tbl: tbl[key] = rnddist(nX)
        return tbl[key][x]
    r = F(random.randint(0, 4), 4); b = random.randint(0, 2); N = random.randint(1, 3)
    kv = [F(random.randint(0, 4), 4) for _ in range(8)]
    kap = lambda j, kv=kv: kv[j] if j < len(kv) else F(1)
    nh = random.randint(0, 4)
    h = sum(push[z] * phi[z] for z in range(nZ))
    S = survH(h, kap, nh, 0)
    risk = S * cat(Bad, M, phi, pi, r, b, N, 0, ())
    bads = [x for x in range(nX) if Bad[x]]
    if bads:
        one = max(S * capB(r, b, sum(M[x][z] * phi[z] for z in range(nZ))) for x in bads)
    else:
        one = F(0)
    if risk > one: viol += 1; print("R VIOL", risk, one)
print("R reduction violations:", viol)

# ---- (W) witness numerics
f = lambda t: binCDF(12, 1, t) * t
best = max((f(F(k, 10000)), F(k, 10000)) for k in range(0, 10001, 5))
print("m=12 sc=1: max_t t*binCDF ~", float(best[0]), "at", best[1])
def grid_ok(ts, U, fsurv, fcap):
    return all(fsurv(a) * fcap(c) <= U for a, c in zip(ts, ts[1:]))

def greedy(fsurv, fcap, U, den):
    ts = [F(0)]
    while ts[-1] < 1:
        a = ts[-1]; best = None
        for k in range(int(a * den) + 1, den + 1):
            c = F(k, den)
            if fsurv(a) * fcap(c) <= U: best = c
            else: break
        if best is None: return None
        ts.append(best)
    return ts

for U, den in [(F(7, 100), 100), (F(7, 100), 1000), (F(71, 1000), 100), (F(8, 100), 100), (F(75, 1000), 100)]:
    ts = greedy(lambda a: binCDF(12, 1, a), lambda c: min(F(1), c), U, den)
    print("U", U, "den", den, "points", None if ts is None else len(ts), ts if ts and len(ts) < 40 else "")

# ---- witness grid exact check
WG = [F(0), F(7,100), F(9,100), F(1,10), F(11,100), F(3,25), F(13,100), F(7,50), F(3,20), F(4,25), F(9,50), F(11,50), F(33,100), F(1)]
ok = all(a <= c and binCDF(12,1,a) * c <= F(3,40) for a, c in zip(WG, WG[1:]))
slack = min(F(3,40) - binCDF(12,1,a) * c for a, c in zip(WG, WG[1:]))
print("witness grid ok:", ok, "min slack", float(slack), " lower point", float(binCDF(12,1,F(1,8))*F(1,8)), ">= 17/250?", binCDF(12,1,F(1,8))*F(1,8) >= F(17,250))

# ---- (S1) stratified certificate on random instances (arbitrary K, possibly non-decodable)
def stratcat_seed(Bad, K, cl, Es, m, sc, r, b, N, phi, pi):
    M = [K[cl[x]] for x in range(len(cl))]
    ss = F(1)
    for e in Es:
        h = sum(K[e][z] * phi[z] for z in range(len(phi)))
        ss *= binCDF(m, sc, h)
    return ss * cat(Bad, M, phi, pi, r, b, N, 0, ())
viol = 0
for trial in range(200):
    nC, nZ = random.randint(1, 3), random.randint(2, 3)
    K = [rnddist(nZ) for _ in range(nC)]
    nX = random.randint(1, 3); cl = [random.randrange(nC) for _ in range(nX)]
    Bad = [random.random() < 0.6 for _ in range(nX)]
    Es = sorted(set(cl[x] for x in range(nX) if Bad[x]) | set(random.sample(range(nC), random.randint(0, nC))))
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    tbl = {}
    def pi(hist, x, tbl=tbl, nX=nX):
        if hist not in tbl: tbl[hist] = rnddist(nX)
        return tbl[hist][x]
    r = F(random.randint(0, 4), 4); b = random.randint(0, 2); N = random.randint(0, 3)
    m = random.randint(0, 5); sc = random.randint(0, 2)
    risk = stratcat_seed(Bad, K, cl, Es, m, sc, r, b, N, phi, pi)
    # certificate value: sup over t grid (fine) of binCDF*capB; risk must be <= value at t = worst bad class pass rate
    bads = [x for x in range(nX) if Bad[x]]
    hstar = max([sum(K[cl[x]][z] * phi[z] for z in range(nZ)) for x in bads], default=F(0))
    if risk > binCDF(m, sc, hstar) * capB(r, b, hstar): viol += 1; print("S1 VIOL", risk)
print("S1 violations:", viol)
