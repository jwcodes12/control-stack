"""UMUSE brute-force checks (exact, no sampling).

1. honest halt recursion == 1 - binCDF(N, b, f0)   (iid honest task stream, stateless honest monitor)
2. slack lemma: binCDF(n, s, a) >= 1 - eps  =>  s >= n (a - eps)
3. frontier at realistic budgets: global hard slack vs class-aware slack sized for honest false shutdown <= eps;
   exact colluder risk sup_t t * P(survive) (b = 0, r = 1, stratified design m = n/k per class, decodable mediator)
   versus the floors min(1/2, k(a-eps)/4) (global, via UMLOWERF1) and the mimicry floor (1-eps) a.
"""
from fractions import Fraction as F
from math import comb
import itertools, random

def binCDF(n, s, h):
    return sum(comb(n, j) * h**j * (1-h)**(n-j) for j in range(0, min(s, n)+1)) if s >= 0 else 0*h

# 1. halt recursion with a random finite instance (exact rationals)
def haltP(M, phi, mu, b, n, u):
    if n == 0: return F(0)
    tot = F(0)
    for x, px in enumerate(mu):
        for z, mz in enumerate(M[x]):
            flag = 1 - phi[z]
            tot += px * mz * (phi[z] * haltP(M, phi, mu, b, n-1, u) +
                              flag * (haltP(M, phi, mu, b, n-1, u+1) if u < b else F(1)))
    return tot

random.seed(1)
def rdist(k):
    w = [random.randint(0, 5) for _ in range(k)]
    if sum(w) == 0: w[0] = 1
    return [F(v, sum(w)) for v in w]
for trial in range(200):
    X, Z = random.randint(1, 3), random.randint(1, 3)
    M = [rdist(Z) for _ in range(X)]
    phi = [F(random.randint(0, 4), 4) for _ in range(Z)]
    mu = rdist(X)
    b, N = random.randint(0, 3), random.randint(0, 4)
    f0 = sum(mu[x] * M[x][z] * (1 - phi[z]) for x in range(X) for z in range(Z))
    assert haltP(M, phi, mu, b, N, 0) == 1 - binCDF(N, b, f0), (trial,)
print("1. halt recursion == 1 - binCDF(N,b,f0): 200 random exact instances OK")

# 2. slack lemma, exact on a grid
bad = 0
for n in range(0, 25):
    for s in range(0, n+2):
        for a in [F(i, 20) for i in range(21)]:
            for eps in [F(i, 20) for i in range(21)]:
                if binCDF(n, s, a) >= 1 - eps and not (s >= n * (a - eps)):
                    bad += 1
print("2. Markov slack lemma (s >= n(a-eps)) counterexamples on grid:", bad)
# 2b. Chebyshev slack lemma: binCDF(n,s,a) >= 1-eps, eps<1, s < n a  =>  (n a - s)^2 <= n a (1-a)/(1-eps)
bad = 0
for n in range(0, 25):
    for s in range(0, n+2):
        for a in [F(i, 20) for i in range(21)]:
            for eps in [F(i, 20) for i in range(20)]:
                if binCDF(n, s, a) >= 1 - eps and s < n*a and not ((n*a - s)**2 <= n*a*(1-a)/(1-eps)):
                    bad += 1
print("2b. Chebyshev slack lemma counterexamples on grid:", bad)

# 3. frontier (floats; pmf by recurrence to avoid huge binomials)
def fbinCDF(n, s, h):
    if s < 0: return 0.0
    if h <= 0: return 1.0
    if h >= 1: return 1.0 if s >= n else 0.0
    from math import lgamma, log, exp
    return min(1.0, sum(exp(lgamma(n+1)-lgamma(j+1)-lgamma(n-j+1)+j*log(h)+(n-j)*log(1-h)) for j in range(0, min(s, n)+1)))
def sup_t(f, grid=2000):
    best, bt = 0.0, 0.0
    for i in range(grid+1):
        t = i/grid; v = f(t)
        if v > best: best, bt = v, t
    return best, bt

eps = 0.10
print(f"3. frontier, eps = {eps} (honest false shutdown <= eps), b = 0, r = 1, decodable, stratified m = n/k")
print(" n_h  a0    k | global n_s  risk_glob  floor Cheb+UMLOWER   | class s_c  risk_cls | mimicry (1-eps)a")
for nh, a0, k in [(30, .01, 4), (30, .05, 4), (100, .01, 4), (100, .01, 8), (100, .05, 8), (100, .05, 16),
                  (1000, .05, 8), (1000, .01, 8), (10000, .05, 8)]:
    m = nh // k
    ns = next(s for s in range(nh+1) if fbinCDF(nh, s, a0) >= 1 - eps)
    rg, _ = sup_t(lambda t: t * fbinCDF(m, ns, t))          # colluder passes its own class; m honeypots of it
    sc = next(s for s in range(m+1) if fbinCDF(m, s, a0) ** k >= 1 - eps)
    rc, _ = sup_t(lambda t: t * fbinCDF(m, sc, t))
    # Chebyshev slack lemma: ns >= n a - sqrt(n a (1-a)/(1-eps)); then UMLOWERF1 at the best t
    sl = max(nh*a0 - (nh*a0*(1-a0)/(1-eps))**.5, 0) + 1
    fl = min(.5, k * sl / (4 * nh))
    print(f"{nh:5d} {a0:.2f} {k:3d} | {ns:5d} {rg:9.3f} {fl:9.3f}            | {sc:5d} {rc:9.3f} | {(1-eps)*a0:.4f}")
