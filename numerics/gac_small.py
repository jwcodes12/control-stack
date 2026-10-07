"""Search tiny GAC-style instances (M = 2, 3; C = 1) where a clocked blind Red beats every fixed beta."""
from fractions import Fraction as F
import itertools
exec(open('gac_explore.py').read().split('for (M, C, kind)')[0])

def clocked_best(M, C, qa, qd):
    # deterministic clocked policies: attack set A subset of rounds (by remaining m); Red sees nothing else
    best = None
    for mask in range(1 << M):
        pol = lambda m, mask=mask: 'B' if (mask >> (m - 1)) & 1 else 'S'
        memo = {}
        def U(m, c):
            if m == 0: return F(0)
            if (m, c) in memo: return memo[(m, c)]
            v = sum(p * (1 if o == 'cat' else 0 if o == 'safe' else U(*o)) for p, o in step(m, c, pol(m), qa, qd))
            memo[(m, c)] = v; return v
        v = U(M, C)
        if best is None or v > best[0]: best = (v, bin(mask))
    return best

res = []
for M in (2, 3):
    for qa1 in [F(1,4), F(1,3), F(1,2)]:
        for front in [True, False]:
            C = 1
            def qa(m, c, qa1=qa1, front=front, M=M):
                if c == 0: return F(0)
                return qa1 if (m == M or not front) else qa1 / 2
            def qd(m, c, qa=qa): return min(F(1), qa(m, c) + F(1, 10))
            fb = max((fixed_beta(M, C, qa, qd, F(i, 400)), F(i, 400)) for i in range(401))
            cb = clocked_best(M, C, qa, qd)
            fi = full_info(M, C, qa, qd)
            res.append((M, qa1, front, float(fb[0]), fb[1], float(cb[0]), cb[1], float(fi)))
for r in res: print(r)
