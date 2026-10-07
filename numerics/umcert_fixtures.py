"""UMCERT v1 Witness fixtures: exact grid certificates (Fractions)."""
from fractions import Fraction as F
from math import comb
def binCDF(n, s, h):
    return sum(F(comb(n, j)) * h**j * (1 - h)**(n - j) for j in range(s + 1) if j <= n)
def capB(r, b, a): return 1 - r + r * a if b > 0 else a
def greedy(S, Fc, U, cands):
    ts = [F(0)]
    while ts[-1] < 1:
        a = ts[-1]; best = None
        for c in cands:
            if c <= a: continue
            if S(a) * Fc(c) <= U: best = c
            else: break
        if best is None: return None
        ts.append(best)
    return ts
def check(S, Fc, U, ts):
    return ts[0] == 0 and ts[-1] == 1 and all(a <= c and S(a) * Fc(c) <= U for a, c in zip(ts, ts[1:]))
def fmax(f, den):
    return max((f(F(i, den)), F(i, den)) for i in range(den + 1))
c1000 = [F(i, 1000) for i in range(1, 1001)]
c_fine = sorted(set([F(i, 10000) for i in range(1, 3001)] + [F(i, 1000) for i in range(300, 1001)]))

# (i) main: m = n_h = 12, s_c = n_s = 1, r = 1, b = 1
S1 = lambda t: binCDF(12, 1, t); F1 = lambda t: t
g1 = greedy(S1, F1, F(7, 100), c1000); print("main", len(g1), check(S1, F1, F(7,100), g1), g1)
print(" lower", binCDF(12,1,F(1,8))*F(1,8) >= F(6833,100000))
# (ii) soft slack: survH t (const 1/5) 100 0 = (1 - t/5)^100, L = 1, r = 1, b = 1
S2 = lambda t: (1 - t / 5) ** 100
v2, t2 = fmax(lambda t: S2(t) * t, 2000); print("soft max", float(v2), t2, "counting 5/101 =", 5/101)
g2 = greedy(S2, F1, F(19, 1000), c_fine); print("soft", len(g2) if g2 else None, check(S2, F1, F(19,1000), g2) if g2 else None, g2)
print(" soft lower at t=1/20:", float(S2(F(1,20))*F(1,20)), S2(F(1,20))*F(1,20) >= F(18,1000))
# (iii) kink + imperfect recall: n_h = 30, n_s = 1, L = 4, r = 9/10, b = 1
S3 = lambda t: binCDF(30, 1, t); F3 = lambda t: capB(F(9,10), 1, min(F(1), 4 * t))
v3, t3 = fmax(lambda t: S3(t) * F3(t), 20000); print("kink max", float(v3), t3, "counting", float(F(1,10) + F(9,10) * 4 * F(2, 31)))
for U in [F(2,10), F(21,100), F(205,1000)]:
    g3 = greedy(S3, F3, U, c_fine)
    print(" kink U", U, len(g3) if g3 else None, check(S3, F3, U, g3) if g3 else None)
for U in [F(17,100), F(165,1000)]:
    g3 = greedy(S3, F3, U, c_fine)
    print(" kink U", U, len(g3) if g3 else None, check(S3, F3, U, g3) if g3 else None, g3)
print(" kink lower at t=7/200:", float(S3(F(7,200))*F3(F(7,200))), S3(F(7,200))*F3(F(7,200)) >= F(16,100))
