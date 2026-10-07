"""DESIGN §5 table as UMCERT certificates (exact Fractions).
X_strat(m, s_c) = max_t binCDF(m, s_c, t) * t           (stratified, content-only, exact decoding, r = 1; UMCERT S2)
X_global(n_h, n_s, k) = max_t binCDF(n_h, n_s, t) * min(1, k t)  (uniform honeypots over k decodable classes, L = k;
                         exact by UMCERT R since psi = t on one class attains E_x psi = k E_PH psi)"""
from fractions import Fraction as F
from math import comb, ceil

def binCDF(n, s, h):
    return sum(F(comb(n, j)) * h**j * (1 - h)**(n - j) for j in range(s + 1) if j <= n)

def fmax(f, den=4000):
    return max((f(F(i, den)), F(i, den)) for i in range(den + 1))

def greedy(S, Fc, U, den):
    ts = [F(0)]
    while ts[-1] < 1:
        a = ts[-1]; best = None
        lo = int(a * den) + 1
        for k in range(lo, den + 1):
            c = F(k, den)
            if S(a) * Fc(c) <= U: best = c
            else: break
        if best is None: return None
        ts.append(best)
    return ts

rows = [(30, 0, 4, 0, 7, 0), (30, F(1,100), 4, 1, 7, 1), (30, F(5,100), 4, 3, 7, 2), (100, 0, 8, 0, 12, 0),
        (100, F(1,100), 4, 2, 25, 1), (100, F(1,100), 8, 2, 12, 1), (100, F(5,100), 8, 8, 12, 3), (100, F(5,100), 16, 8, 6, 2)]
for (nh, a0, k, ns, m, sc) in rows:
    vg, tg = fmax(lambda t: binCDF(nh, ns, t) * min(F(1), k * t))
    vs, ts_ = fmax(lambda t: binCDF(m, sc, t) * t)
    Ug = F(ceil(float(vg) * 1000 + 1), 1000); Us = F(ceil(float(vs) * 1000 + 1), 1000)
    gg = greedy(lambda a: binCDF(nh, ns, a), lambda c: min(F(1), k * c), Ug, 1000)
    gs = greedy(lambda a: binCDF(m, sc, a), lambda c: c, Us, 1000)
    print(f"n_h={nh} a0={float(a0)} k={k} | global n_s={ns}: max={float(vg):.4f} at {float(tg):.4f}, U={Ug} grid={len(gg) if gg else None}"
          f" | strat m={m} s_c={sc}: max={float(vs):.4f} at {float(ts_):.4f}, U={Us} grid={len(gs) if gs else None}")

print("--- global rows with a geometric grid (fine near 0)")
def greedy2(S, Fc, U, cands):
    ts = [F(0)]; i = 0
    while ts[-1] < 1:
        a = ts[-1]; best = None
        for c in cands:
            if c <= a: continue
            if S(a) * Fc(c) <= U: best = c
            else: break
        if best is None: return None
        ts.append(best)
    return ts
cands = sorted(set([F(i, 20000) for i in range(1, 2001)] + [F(i, 1000) for i in range(100, 1001)]))
for (nh, a0, k, ns, m, sc) in rows:
    vg, tg = fmax(lambda t: binCDF(nh, ns, t) * min(F(1), k * t), den=20000)
    Ug = F(ceil(float(vg) * 1000 + 1), 1000)
    gg = greedy2(lambda a: binCDF(nh, ns, a), lambda c: min(F(1), k * c), Ug, cands)
    print(f"n_h={nh} k={k} n_s={ns}: max={float(vg):.4f} U={Ug} grid={len(gg) if gg else None}")
