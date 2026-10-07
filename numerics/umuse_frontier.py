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

# 3. frontier (v2, after Reviewer A's design review: designs separated, balanced allocation, grid sup labelled)
from math import lgamma, log, exp
def fbinCDF(n, s, h):
    """P(Bin(n,h) <= s) in floats (log-gamma summation)."""
    if s < 0: return 0.0
    if h <= 0: return 1.0
    if h >= 1: return 1.0 if s >= n else 0.0
    return min(1.0, sum(exp(lgamma(n+1)-lgamma(j+1)-lgamma(n-j+1)+j*log(h)+(n-j)*log(1-h)) for j in range(0, min(s, n)+1)))
def grid_sup(f, grid=2000):
    """max over t = i/grid of f(t); a GRID APPROXIMATION of sup_t (error <= 1/grid for these monotone-CDF curves)."""
    return max(f(i/grid) for i in range(grid+1))

eps, f0, N, b = 0.10, 0.01, 100, 3
print(f"3. frontier: honest false shutdown <= eps = {eps}; r = 1, b = 0 for risk; class-only (decodable, content-only) views;")
print(f"   the colluder passes ONE class at rate t. Usefulness column: full completion S * binCDF(N, b, f0) at N={N}, b={b}, f0={f0}.")
print("   'iid' = PL_UMPROTF1's iid honeypots, uniform class masses: sup_t t*binCDF(n_h, n_s, t/k).")
print("   'strat' = balanced deterministic allocation m_c (sum n_h), GLOBAL counter: sup_t t*binCDF(min_c m_c, n_s, t) (colluder picks the smallest class).")
print("   'class' = balanced allocation with per-class slack s_c: honest survival prod_c binCDF(m_c, s_c, a0).")
print("   All sup_t values are grid approximations (grid 1/2000).")
print(" n_h   a0   k | n_s  iid_glob strat_glob | s_c  class  | completion(global) completion(class) | floor a0*u")
for nh, a0, k in [(30, .01, 4), (30, .05, 4), (100, .01, 4), (100, .01, 8), (100, .05, 8), (100, .05, 16),
                  (1000, .05, 8), (1000, .01, 8), (10000, .05, 8)]:
    ms = [nh // k + (1 if c < nh % k else 0) for c in range(k)]
    ns = next(s for s in range(nh+1) if fbinCDF(nh, s, a0) >= 1 - eps)
    rg_iid = grid_sup(lambda t: t * fbinCDF(nh, ns, t / k))
    rg_str = grid_sup(lambda t: t * fbinCDF(min(ms), ns, t))
    def honest_cls(sc): 
        p = 1.0
        for m in ms: p *= fbinCDF(m, sc, a0)
        return p
    sc = next(s for s in range(max(ms)+1) if honest_cls(s) >= 1 - eps)
    rc = grid_sup(lambda t: t * fbinCDF(min(ms), sc, t))
    D = fbinCDF(N, b, f0)
    ug, uc = fbinCDF(nh, ns, a0) * D, honest_cls(sc) * D
    print(f"{nh:5d} {a0:.2f} {k:3d} | {ns:4d} {rg_iid:8.3f} {rg_str:9.3f}  | {sc:4d} {rc:6.3f} | {ug:17.3f} {uc:18.3f} | {a0*min(ug,uc):.4f}")
