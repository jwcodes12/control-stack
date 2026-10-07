"""Brute-force checks of the candidate T3 ingredients (exact rationals where possible).

(1) sup_h h * P(Bin(n,h) <= s)  <=  (s+1)/(n+1)       [claimed closed form]
(2) identity: h*P(Bin(n,h)<=s) = (1/(n+1)) * E[X 1{1<=X<=s+1}],  X ~ Bin(n+1,h)
(3) F*(L) = sup_h min(1, L h) P(Bin(n,h)<=s) and its ratio to L(s+1)/(n+1)
"""
from fractions import Fraction as Fr
from math import comb
import itertools

def B(n, s, h):
    return sum(comb(n, j) * h**j * (1 - h)**(n - j) for j in range(0, s + 1))

def sup_grid(f, steps=20000):
    best, arg = -1, None
    for i in range(steps + 1):
        h = i / steps
        v = f(h)
        if v > best:
            best, arg = v, h
    return best, arg

worst_ratio = 0
for n in range(0, 41):
    for s in range(0, n + 1):
        # identity check at rational points
        for h in [Fr(1, 7), Fr(2, 5), Fr(9, 10)]:
            lhs = h * B(n, s, h)
            rhs = Fr(1, n + 1) * sum(x * comb(n + 1, x) * h**x * (1 - h)**(n + 1 - x) for x in range(1, s + 2))
            assert lhs == rhs, (n, s, h)
        v, arg = sup_grid(lambda h: h * B(n, s, h), 2000)
        bound = (s + 1) / (n + 1)
        assert v <= bound + 1e-12, (n, s, v, bound)
        worst_ratio = max(worst_ratio, v / bound)
print("identity (2) exact on n<=40; bound (1) holds; max sup/bound ratio =", round(worst_ratio, 4))

# (3) F* vs closed form at illustrative parameters
for (L, n, s) in [(1, 100, 0), (1, 100, 5), (8, 1000, 2), (8, 5000, 10), (10, 100, 5), (32, 10000, 20), (1024, 100000, 5)]:
    fstar, arg = sup_grid(lambda h: min(1.0, L * h) * B(n, s, h), 20000)
    print(f"L={L:5d} n_h={n:6d} n_s={s:3d}  F*={fstar:.4f} at h={arg:.5f}   closed form L(n_s+1)/(n_h+1)={min(1, L*(s+1)/(n+1)):.4f}")
