"""UMDEFER brute force (exact rationals).
Protocol: as PL_UMPROTF1.cat, except a FLAG with no audit left (u >= b) halts w.p. eta and otherwise DEFERS
(the submission is replaced by trusted output; deployment continues at the same u). A deferred BAD submission is
incriminated (audited) w.p. q: caught w.p. r -> absorbing shutdown; otherwise the protocol continues (retry).
Checks:
 (a) catD <= max(1 - r + r A, A / theta), theta = eta + (1-eta) q r > 0, A >= pass prob of every bad view law;
     for random history-dependent generators, random mediators/rules.
 (c) no-go at theta = 0: identity mediator, honeypots = point mass on the attack (L = 1), colluder flags
     everything except the attack view (passes it w.p. t), generator burns b audits on a benign x0 then attacks:
     protocol value = binCDF(nh, ns, t) * (1 - (1-t)^(N-b)).
"""
from fractions import Fraction as F
from math import comb
import random, itertools
random.seed(7)

def binCDF(n, s, h): return sum(comb(n, j) * h**j * (1-h)**(n-j) for j in range(min(s, n)+1))

def catD(X, Bad, M, phi, pi, r, b, eta, q, n, u, h):
    if n == 0: return F(0)
    tot = F(0)
    for x in X:
        px = pi(h, x)
        if px == 0: continue
        for z, mz in enumerate(M[x]):
            if mz == 0: continue
            hp, hf = h + ((x, z, True),), h + ((x, z, False),)
            vp = F(1) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u, hp)
            if u < b:
                vf = (1 - r) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u+1, hf)
            else:
                cont = catD(X, Bad, M, phi, pi, r, b, eta, q, n-1, u, hf)
                vf = (1 - eta) * ((1 - q*r) * cont if Bad[x] else cont)
            tot += px * mz * (phi[z] * vp + (1 - phi[z]) * vf)
    return tot

def rd(k):
    w = [random.randint(0, 4) for _ in range(k)]
    if sum(w) == 0: w[random.randrange(k)] = 1
    return [F(v, sum(w)) for v in w]

worst = None; cnt = 0
for trial in range(400):
    nX, nZ = random.randint(1, 3), random.randint(1, 3)
    X = list(range(nX)); Bad = [random.random() < .5 for _ in X]
    if not any(Bad): Bad[0] = True
    M = [rd(nZ) for _ in X]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    table = {}
    def pi(h, x, table=table, nX=nX):
        if h not in table: table[h] = rd(nX)
        return table[h][x]
    r = F(random.randint(0, 4), 4); eta = F(random.randint(0, 4), 4); q = F(random.randint(0, 4), 4)
    b = random.randint(0, 2); N = random.randint(1, 4)
    theta = eta + (1 - eta) * q * r
    if theta == 0: continue
    A = max(sum(M[x][z] * phi[z] for z in range(nZ)) for x in X if Bad[x])
    v = catD(X, Bad, M, phi, pi, r, b, eta, q, N, 0, ())
    bound = max(1 - r + r*A, A / theta)
    cnt += 1
    gap = bound - v
    if worst is None or gap < worst[0]: worst = (gap, dict(r=r, eta=eta, q=q, b=b, N=N, A=A, v=v, bound=bound))
    assert v <= bound and v <= 1, (trial, v, bound)
print(f"(a) catD <= max(1-r+rA, A/theta): {cnt} random instances OK; tightest gap {worst[0]} at {worst[1]}")

# (c) no-go value at theta = 0 (eta = q = 0): exact protocol value of the explicit colluder
def nogo(nh, ns, b, N, t, r):
    # X = {0 (benign x0), 1 (attack)}, identity mediator; monitor passes view 1 w.p. t, flags view 0
    X = [0, 1]; Bad = [False, True]; M = [[F(1), F(0)], [F(0), F(1)]]; phi = [F(0), t]
    def pi(h, x):
        used = sum(1 for (_, _, p) in h if not p)    # benign flags so far = audits used (deployment only)
        want = 0 if used < b else 1
        return F(1) if x == want else F(0)
    S = binCDF(nh, ns, t)   # honeypots = point mass on the attack: each passes w.p. t
    return S * catD(X, Bad, M, phi, pi, r, b, F(0), F(0), N, 0, ())
for (nh, ns, b, N, t, r) in [(3, 0, 1, 4, F(1, 4), F(1)), (4, 1, 2, 6, F(1, 3), F(1, 2)), (2, 0, 0, 5, F(1, 5), F(0))]:
    v = nogo(nh, ns, b, N, t, r)
    pred = binCDF(nh, ns, t) * (1 - (1 - t)**(N - b))
    assert v == pred, (v, pred)
print("(c) no-go value == binCDF(nh,ns,t) * (1-(1-t)^(N-b)) on 3 exact instances OK")
# scale: sup_t binCDF(nh, ns, t) (1-(1-t)^K)
for (nh, ns, K) in [(30, 1, 30), (30, 1, 300), (100, 5, 100), (100, 5, 1000), (100, 5, 10000)]:
    best = max(binCDF(nh, ns, i/20000) * (1 - (1 - i/20000)**K) for i in range(1, 20001))
    print(f"   n_h={nh} n_s={ns} K=N-b={K}: sup_t value = {best:.3f}")

# (a') sharper: catD <= max([u<b](1 - r + r A), A / (theta + A (1 - theta)))  ; (e) eta = 1 recovers PL_UMPROTF1.cat
def cat(X, Bad, M, phi, pi, r, b, n, u, h):
    if n == 0: return F(0)
    tot = F(0)
    for x in X:
        px = pi(h, x)
        if px == 0: continue
        for z, mz in enumerate(M[x]):
            hp, hf = h + ((x, z, True),), h + ((x, z, False),)
            vp = F(1) if Bad[x] else cat(X, Bad, M, phi, pi, r, b, n-1, u, hp)
            vf = (((1 - r) if Bad[x] else cat(X, Bad, M, phi, pi, r, b, n-1, u+1, hf)) if u < b else F(0))
            tot += px * mz * (phi[z] * vp + (1 - phi[z]) * vf)
    return tot
cnt = 0; tight = []
for trial in range(400):
    nX, nZ = random.randint(1, 3), random.randint(1, 3)
    X = list(range(nX)); Bad = [random.random() < .5 for _ in X]
    if not any(Bad): Bad[0] = True
    M = [rd(nZ) for _ in X]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    table = {}
    def pi(h, x, table=table, nX=nX):
        if h not in table: table[h] = rd(nX)
        return table[h][x]
    r = F(random.randint(0, 4), 4); eta = F(random.randint(0, 4), 4); q = F(random.randint(0, 4), 4)
    b = random.randint(0, 2); N = random.randint(1, 4); u0 = random.randint(0, 2)
    assert catD(X, Bad, M, phi, pi, r, b, F(1), q, N, u0, ()) == cat(X, Bad, M, phi, pi, r, b, N, u0, ())
    theta = eta + (1 - eta) * q * r
    if theta == 0: continue
    A = max(sum(M[x][z] * phi[z] for z in range(nZ)) for x in X if Bad[x])
    v = catD(X, Bad, M, phi, pi, r, b, eta, q, N, u0, ())
    t2 = A / (theta + A * (1 - theta)) if theta + A * (1 - theta) > 0 else F(0)
    bound = max((1 - r + r*A) if u0 < b else F(0), t2)
    assert v <= bound, (trial, v, bound)
    cnt += 1
print(f"(a') sharper bound OK on {cnt} instances; (e) eta = 1 gives cat exactly on 400 instances")
# tightness of the deferral term: always-attack colluder, budget exhausted (b = 0), horizon N
for (a, eta, q, r, N) in [(F(1,10), F(0), F(1,2), F(1), 30), (F(1,4), F(1,10), F(1,4), F(1,2), 30)]:
    X = [0]; Bad = [True]; M = [[F(1)]]; phi = [a]
    v = catD(X, Bad, M, phi, lambda h, x: F(1), r, 0, eta, q, N, 0, ()) if N <= 12 else None
    theta = eta + (1 - eta) * q * r
    c = (1 - a) * (1 - theta)
    exact = a * (1 - c**N) / (1 - c)
    print(f"   always-attack, b=0: a={a} theta={theta} N={N}: value {float(exact):.4f} -> limit {float(a/(theta + a*(1-theta))):.4f}; A/theta = {float(a/theta):.4f}")
