"""TMGAC bridge evidence v2 (round-2 review fixes): genuinely monotone ROC tables, no skipped comparisons;
(Z) checked both for lawful adapters and as an unrestricted algebraic identity (TD not clamped); (UZ) with the
corrected used-solution reward 1 - qd + [c > 0] qa; (W) including TA > 0 at c = 0."""
from fractions import Fraction as F
import random
random.seed(11)
exec(open('tmgac_check.py').read().split('bad = 0')[0])
exec('def vstar' + open('tmgac_check.py').read().split('def vstar')[1].split('def risk_det')[0])
def usedR(qa, qd): return lambda n, c: 1 - qd(n + 1, c) + (qa(n + 1, c) if c > 0 else 0)
bad = cnt = 0
for trial in range(400):
    M, C = random.randint(0, 5), random.randint(0, 3)
    grid = sorted({F(0)} | {F(random.randint(0, 16), 16) for _ in range(6)} | {F(1)})
    vals = sorted(F(random.randint(0, 16), 16) for _ in grid); vals[0] = F(0)          # monotone, f(0) = 0
    fmap = dict(zip(grid, vals)); f = lambda q, fmap=fmap: fmap[q]
    tab_a = {(m, c): (random.choice(grid) if c > 0 else F(0)) for m in range(M + 2) for c in range(C + 1)}
    tab_d = {k: random.choice([g for g in grid if g >= v]) for k, v in tab_a.items()}
    qa = lambda m, c: tab_a[(m, c)]; qd = lambda m, c: tab_d[(m, c)]
    TA = lambda n, c: f(qa(n + 1, c)); TD = lambda n, c: f(qd(n + 1, c)); FA = lambda n, c: qa(n + 1, c)
    for beta in (F(0), F(1, 3), F(3, 4), F(1)):
        cnt += 1
        if 1 - risk_const(beta, M, C, TA, TD, FA) != zGAC(f, qa, qd, beta, M, C): bad += 1
    cnt += 1
    if honest(M, C, TA, TD, FA, usedR(qa, qd)) != uGAC(qa, qd, M, C): bad += 1
    # unrestricted algebraic identity: arbitrary (possibly non-monotone, out-of-range) f values and beta
    g = {q: F(random.randint(-8, 24), 16) for q in grid}; g[F(0)] = F(0)
    fg = lambda q, g=g: g[q]
    TAg = lambda n, c: fg(qa(n + 1, c)); TDg = lambda n, c: fg(qd(n + 1, c))
    b = F(random.randint(-4, 8), 4); cnt += 1
    if 1 - risk_const(b, M, C, TAg, TDg, FA) != zGAC(fg, qa, qd, b, M, C): bad += 1
print(f"bridge comparisons: {cnt}, mismatches: {bad}")
# (W) with TA > 0 at c = 0
wb = 0
for trial in range(200):
    N = random.randint(0, 6)
    ta = {n: F(random.randint(0, 8), 8) for n in range(N)}; td = {n: max(ta[n], F(random.randint(0, 8), 8)) for n in range(N)}
    T1 = lambda n, c: ta[n]; T2 = lambda n, c: td[n]; Z0 = lambda n, c: F(0)
    if risk_const(F(1), N, 0, T1, T2, Z0) != vstar(N, 0, T1, T2, Z0): wb += 1
print("(W) with TA > 0 at c = 0: mismatches", wb, "/ 200")
