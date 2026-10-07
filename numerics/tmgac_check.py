"""TMGAC checks (exact; uGAC corrected per GAC App. C.2: audited safe solutions are USED, reward 1 - qd + qa): (Z) 1 - risk(constRed beta) on gac = zGAC (Reviewer B's App. C form) when qa(m,0) = 0, f(0) = 0;
(UZ) honest reward of gac's safe rows with rew = 1 - qd(n+1,c) equals uGAC; (T5') exG3 numbers; (WLOG) C = 0."""
from fractions import Fraction as F
import random
random.seed(3)
def gac_rows(n, c, a, TA, TD, FA):
    # returns (cat, {c': K})
    if a:
        cat = (1 - TD(n, c)) if c > 0 else (1 - TD(n, c) + TA(n, c))
        return cat, {c: TD(n, c) - TA(n, c)}
    if c > 0: return F(0), {c - 1: FA(n, c), c: 1 - FA(n, c)}
    return F(0), {c: F(1)}
def risk_const(beta, m, c, TA, TD, FA):
    if m == 0: return F(0)
    n = m - 1; tot = F(0)
    for a, pa in ((True, beta), (False, 1 - beta)):
        cat, K = gac_rows(n, c, a, TA, TD, FA)
        tot += pa * (cat + sum(k * risk_const(beta, n, c2, TA, TD, FA) for c2, k in K.items()))
    return tot
def zGAC(f, qa, qd, beta, m, c):
    if m == 0: return F(1)
    if c == 0: return (1 - beta + beta * f(qd(m, 0))) * zGAC(f, qa, qd, beta, m - 1, 0)
    return (beta * f(qa(m, c)) + (beta * (f(qd(m, c)) - f(qa(m, c))) + (1 - beta) * (1 - qa(m, c))) * zGAC(f, qa, qd, beta, m - 1, c)
            + (1 - beta) * qa(m, c) * zGAC(f, qa, qd, beta, m - 1, c - 1))
def uGAC(qa, qd, m, c):
    if m == 0: return F(0)
    if c == 0: return (1 - qd(m, 0)) + uGAC(qa, qd, m - 1, 0)
    return ((1 - qd(m, c)) + qa(m, c)) + qa(m, c) * uGAC(qa, qd, m - 1, c - 1) + (1 - qa(m, c)) * uGAC(qa, qd, m - 1, c)
def honest(m, c, TA, TD, FA, rew):
    if m == 0: return F(0)
    n = m - 1; cat, K = gac_rows(n, c, False, TA, TD, FA)
    return rew(n, c) + sum(k * honest(n, c2, TA, TD, FA, rew) for c2, k in K.items())
bad = 0
for trial in range(300):
    M, C = random.randint(0, 5), random.randint(0, 3)
    tab_a = {(m, c): (F(random.randint(0, 4), 8) if c > 0 else F(0)) for m in range(M + 2) for c in range(C + 1)}
    tab_d = {k: min(F(1), v + F(random.randint(0, 4), 8)) for k, v in tab_a.items()}
    qa = lambda m, c: tab_a[(m, c)]; qd = lambda m, c: tab_d[(m, c)]
    ft = {}
    def f(q):  # a random monotone ROC-ish map with f(0) = 0
        if q == 0: return F(0)
        if q not in ft: ft[q] = min(F(1), q * F(random.randint(1, 4)))
        return ft[q]
    TA = lambda n, c: f(qa(n + 1, c)); TD = lambda n, c: max(f(qd(n + 1, c)), f(qa(n + 1, c))); FA = lambda n, c: qa(n + 1, c)
    # ensure f monotone pairs: TD >= TA by construction via max; mirror in zGAC with same f values
    fz = lambda q: f(q)
    for beta in (F(0), F(1, 3), F(1)):
        r = risk_const(beta, M, C, TA, TD, FA)
        z = zGAC(lambda q: f(q), qa, lambda m, c: qd(m, c), beta, M, C)
        # zGAC uses f(qd) directly; equal to TD when f(qd) >= f(qa)
        if all(f(qd(m, c)) >= f(qa(m, c)) for m in range(1, M + 1) for c in range(C + 1)):
            if 1 - r != z: bad += 1; print("Z mismatch", M, C, beta, 1 - r, z)
    u = uGAC(qa, qd, M, C); h = honest(M, C, TA, TD, FA, lambda n, c: 1 - qd(n + 1, c) + qa(n + 1, c))
    if u != h: bad += 1; print("U mismatch", M, C, u, h)
print("Z/U mismatches:", bad)
# exG3
TA3 = lambda n, c: F(3, 4) if c > 0 else F(0); TD3 = lambda n, c: F(3, 4); FA3 = lambda n, c: F(1, 2) if c > 0 else F(0)
for b in [F(0), F(1, 4), F(4, 5), F(1)]:
    r = risk_const(b, 3, 1, TA3, TD3, FA3)
    assert r == F(3, 4) * b - F(21, 32) * b**2 + F(5, 32) * b**3, (b, r)
def vstar(m, c, TA, TD, FA):
    if m == 0: return F(0)
    n = m - 1
    return max(cat + sum(k * vstar(n, c2, TA, TD, FA) for c2, k in K.items()) for cat, K in (gac_rows(n, c, a, TA, TD, FA) for a in (True, False)))
def risk_det(seq, m, c, TA, TD, FA):  # seq[j] = action at round j (j = 0 first)
    if m == 0: return F(0)
    n = m - 1; a = seq[len(seq) - m]
    cat, K = gac_rows(n, c, a, TA, TD, FA)
    return cat + sum(k * risk_det(seq, n, c2, TA, TD, FA) for c2, k in K.items())
print("exG3: Vstar =", vstar(3, 1, TA3, TD3, FA3), " clocked (wait, attack, attack) =", risk_det([False, True, True], 3, 1, TA3, TD3, FA3),
      " sup_beta = 13/50 at 4/5:", risk_const(F(4, 5), 3, 1, TA3, TD3, FA3))
# WLOG C = 0: always attack attains Vstar
for TAx in [F(0)]:
    for TDx in [F(1, 4), F(3, 4)]:
        T = lambda n, c: TDx
        print("C=0, TD", TDx, ": Vstar", vstar(4, 0, lambda n, c: F(0), T, lambda n, c: F(0)), " always-attack", risk_const(F(1), 4, 0, lambda n, c: F(0), T, lambda n, c: F(0)))
V = {0: {0: F(0), 1: F(0)}, 1: {0: F(1,4), 1: F(1,4)}, 2: {0: F(7,16), 1: F(1,4)}, 3: {0: F(37,64), 1: F(11,32)}}
ok = True
for n in range(3):
    for c in (0, 1):
        for a in (True, False):
            cat, K = gac_rows(n, c, a, TA3, TD3, FA3)
            if cat + sum(k * V[n][c2] for c2, k in K.items()) > V[n + 1][c]: ok = False; print("viol", n, c, a)
print("exV3 certificate ok:", ok, [ (n,c,vstar(n,c,TA3,TD3,FA3)) for n in range(4) for c in (0,1)])

# --- round-2 review additions
def risk_pol(pol, m, c, TA, TD, FA):   # pol(c) -> P(backdoor) depends on the current coin count only
    if m == 0: return F(0)
    n = m - 1; tot = F(0)
    for a, pa in ((True, pol(c)), (False, 1 - pol(c))):
        cat, K = gac_rows(n, c, a, TA, TD, FA)
        tot += pa * (cat + sum(k * risk_pol(pol, n, c2, TA, TD, FA) for c2, k in K.items()))
    return tot
print("coinRed on exG3 (backdoor iff no coin):", risk_pol(lambda c: F(1) if c == 0 else F(0), 3, 1, TA3, TD3, FA3), "vs 13/50")
# exG3 as gacQ: f q = min 1 (3q/2); qa = qd = 1/2 while c > 0; qa(m,0) = 0, qd(m,0) = 1/2
f = lambda q: min(F(1), F(3, 2) * q)
qa3 = lambda m, c: F(1, 2) if c > 0 else F(0); qd3 = lambda m, c: F(1, 2)
assert all(f(qa3(n + 1, c)) == TA3(n, c) and f(qd3(n + 1, c)) == TD3(n, c) and qa3(n + 1, c) == FA3(n, c) for n in range(5) for c in (0, 1))
print("exG3 = gacQ (f = min 1 (3q/2), qa = qd = 1/2): ok; corrected usefulness uGAC(3,1) =", uGAC(qa3, qd3, 3, 1))
# small adapter witness: f q = min 1 (3q), qa = (0 | 1/4), qd = (1/4 | 1/2), beta 1/2, m = 2, c = 1
fw = lambda q: min(F(1), 3 * q); qaw = lambda m, c: F(0) if c == 0 else F(1, 4); qdw = lambda m, c: F(1, 4) if c == 0 else F(1, 2)
print("adapter witness: zGAC =", zGAC(fw, qaw, qdw, F(1, 2), 2, 1), " usefulness =", uGAC(qaw, qdw, 2, 1))
# audited-only witness: one problem, one coin, qa = qd = 1
print("audited-only usefulness (m=1,c=1,qa=qd=1):", uGAC(lambda m, c: F(1) if c > 0 else F(0), lambda m, c: F(1), 1, 1))
