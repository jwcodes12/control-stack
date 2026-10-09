"""Exact bounds and exact binomial statistics for the SC-21 sampling validation (standard library only).

- `bound_hidden(N, B, k)` = C(N−k, B) / C(N, B)                        (`EvalIntegrity.sc21_undetected_prob`,
                                                                       `EvalIntegrityAdaptive.sc21_adaptive`)
- `hyp_miss(N, B, k, r)` = Σ_{j ≤ min(k,B)} C(k,j)·C(N−k,B−j)/C(N,B)·(1−r)^j   (`ReservedRecall.hypMiss`,
                                                                       `EvalIntegrityAdaptive.sc21_adaptive_recall`)
Both are computed as exact `Fraction`s.

- `binom_sf(x, n, p)`  = P(X ≥ x) for X ~ Bin(n, p), via the regularized incomplete beta I_p(x, n−x+1);
- `clopper_pearson(x, n, level)`: exact two-sided interval (Beta quantiles by bisection on I).
The incomplete beta uses the standard continued fraction (modified Lentz); `test_sampling.py` checks it against
direct binomial sums.
"""
import math
from fractions import Fraction


def bound_hidden(N, B, k):
    return Fraction(math.comb(N - k, B), math.comb(N, B))


def hyp_miss(N, B, k, r):
    r = Fraction(r)
    return sum((Fraction(math.comb(k, j) * math.comb(N - k, B - j), math.comb(N, B)) * (1 - r) ** j
                for j in range(min(k, B) + 1)), Fraction(0))


def _betacf(a, b, x):
    tiny, eps = 1e-300, 3e-16
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c, d = 1.0, 1.0 - qab * x / qap
    d = 1.0 / (d if abs(d) > tiny else tiny)
    h = d
    for m in range(1, 10000):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + aa / c
        c = c if abs(c) > tiny else tiny
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + aa / c
        c = c if abs(c) > tiny else tiny
        de = d * c
        h *= de
        if abs(de - 1.0) < eps:
            return h
    raise ArithmeticError("betacf did not converge")


def betainc(a, b, x):
    """regularized incomplete beta I_x(a, b)"""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    lbt = math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log1p(-x)
    if x < (a + 1.0) / (a + b + 2.0):
        return math.exp(lbt) * _betacf(a, b, x) / a
    return 1.0 - math.exp(lbt) * _betacf(b, a, 1.0 - x) / b


def binom_sf(x, n, p):
    """P(X >= x), X ~ Bin(n, p)"""
    p = float(p)
    if x <= 0:
        return 1.0
    if x > n:
        return 0.0
    return betainc(x, n - x + 1, p)


def _beta_quantile(q, a, b):
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if betainc(a, b, mid) < q:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def clopper_pearson(x, n, level):
    """exact two-sided `level` interval for a binomial proportion"""
    alpha = 1.0 - level
    lo = 0.0 if x == 0 else _beta_quantile(alpha / 2, x, n - x + 1)
    hi = 1.0 if x == n else _beta_quantile(1 - alpha / 2, x + 1, n - x)
    return lo, hi
