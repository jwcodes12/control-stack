"""UMDEFER v2 brute force (exact rationals). catD with an abstract conditional safe-ending floor alpha (theta = eta +
(1-eta) alpha). Checks:
 (b) finite state bound: catD n u h <= finiteCap r A theta b n u, for theta in [0,1] incl. 0
 (c) attainment: view-blind monitor h + fixed bad x at u >= b: catD = retry h theta n
 closed form: (theta + A(1-theta)) retry A theta n = A (1 - ((1-A)(1-theta))^n)
 (f) no-go for every Bool honeypot law PH: value = binCDF(nh, ns, PH(true) t) (1 - (1-t)^(N-b)), any N (nat subtraction)
 two-round witness: retry suppression 29/200 vs 19/100
"""
from fractions import Fraction as F
from math import comb
import random
random.seed(11)
def binCDF(n, s, h): return sum(comb(n, j) * h**j * (1-h)**max(n-j, 0) for j in range(s+1))
def catD(X, Bad, M, phi, pi, r, b, eta, al, n, u, h):
    if n == 0: return F(0)
    tot = F(0)
    for x in X:
        px = pi(h, x)
        if px == 0: continue
        for z, mz in enumerate(M[x]):
            if mz == 0: continue
            hp, hf = h + ((x, z, True),), h + ((x, z, False),)
            vp = F(1) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, al, n-1, u, hp)
            if u < b:
                vf = (1 - r) if Bad[x] else catD(X, Bad, M, phi, pi, r, b, eta, al, n-1, u+1, hf)
            else:
                vf = (1 - eta) * ((1 - al) if Bad[x] else 1) * catD(X, Bad, M, phi, pi, r, b, eta, al, n-1, u, hf)
            tot += px * mz * (phi[z] * vp + (1 - phi[z]) * vf)
    return tot
def retry(A, th, n):
    v = F(0)
    for _ in range(n): v = A + (1 - A) * (1 - th) * v
    return v
def finiteCap(r, A, th, b, n, u):
    if n == 0: return F(0)
    if u < b: return max(1 - r + r*A, retry(A, th, max(n - (b - u), 0)))
    return retry(A, th, n)
def rd(k):
    w = [random.randint(0, 4) for _ in range(k)]
    if sum(w) == 0: w[random.randrange(k)] = 1
    return [F(v, sum(w)) for v in w]
cnt = 0; tight = 0
for trial in range(600):
    nX, nZ = random.randint(1, 3), random.randint(1, 3)
    X = list(range(nX)); Bad = [random.random() < .5 for _ in X]
    if not any(Bad): Bad[0] = True
    M = [rd(nZ) for _ in X]
    phi = [F(random.randint(0, 4), 4) for _ in range(nZ)]
    table = {}
    def pi(h, x, table=table, nX=nX):
        if h not in table: table[h] = rd(nX)
        return table[h][x]
    r, eta, al = (F(random.randint(0, 4), 4) for _ in range(3))
    b, N, u0 = random.randint(0, 2), random.randint(0, 4), random.randint(0, 3)
    th = eta + (1 - eta) * al
    A = max(sum(M[x][z] * phi[z] for z in range(nZ)) for x in X if Bad[x])
    v = catD(X, Bad, M, phi, pi, r, b, eta, al, N, u0, ())
    cap = finiteCap(r, A, th, b, N, u0)
    assert 0 <= v <= 1 and v <= cap, (trial, v, cap)
    cnt += 1; tight += (v == cap)
print(f"(b) catD <= finiteCap on {cnt} random instances (theta = 0 allowed), {tight} tight")
for trial in range(300):
    A = F(random.randint(0, 8), 8); th = F(random.randint(0, 8), 8); n = random.randint(0, 6)
    assert (th + A*(1 - th)) * retry(A, th, n) == A * (1 - ((1 - A)*(1 - th))**n)
    b, u = random.randint(0, 2), random.randint(0, 3)
    if u >= b:
        r, eta = F(random.randint(0, 4), 4), F(random.randint(0, 4), 4)
        al = F(random.randint(0, 4), 4); th2 = eta + (1 - eta) * al
        v = catD([0], [True], [[F(1)]], [A], lambda h, x: F(1), r, b, eta, al, n, u, ())
        assert v == retry(A, th2, n)
print("(c) attainment at u >= b and the closed form: 300 instances OK")
def nogo(nh, ns, b, N, t, r, PHt):
    X = [0, 1]; Bad = [False, True]; M = [[F(1), F(0)], [F(0), F(1)]]; phi = [F(0), t]
    def pi(h, x):
        used = sum(1 for (_, _, p) in h if not p)
        return F(1) if x == (0 if used < b else 1) else F(0)
    return binCDF(nh, ns, PHt * t) * catD(X, Bad, M, phi, pi, r, b, F(0), F(0), N, 0, ())
for trial in range(60):
    nh, ns, b, N = random.randint(0, 3), random.randint(0, 2), random.randint(0, 2), random.randint(0, 5)
    t, PHt, r = F(random.randint(0, 4), 4), F(random.randint(0, 4), 4), F(random.randint(0, 4), 4)
    v = nogo(nh, ns, b, N, t, r, PHt)
    assert v == binCDF(nh, ns, PHt * t) * (1 - (1 - t)**max(N - b, 0)), (nh, ns, b, N, t, PHt)
    assert v >= (1 - t)**nh * (1 - (1 - t)**max(N - b, 0))
print("(f) no-go equality for every Bool honeypot law and every N, and its point-mass lower bound: 60 instances OK")
w1 = catD([0], [True], [[F(1)]], [F(1, 10)], lambda h, x: F(1), F(1), 0, F(0), F(1, 2), 2, 0, ())
w2 = catD([0], [True], [[F(1)]], [F(1, 10)], lambda h, x: F(1), F(1), 0, F(0), F(0), 2, 0, ())
print("two-round witness: with alpha = 1/2:", w1, " without:", w2)
