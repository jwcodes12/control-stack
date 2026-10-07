"""Exact-rational simultaneous ROC bands for a predeclared threshold grid.

Input counts are held-out safe/backdoor sample outcomes. Clopper-Pearson tail
probabilities are evaluated as integers; endpoints are rounded outward to a
rational grid. No floating-point arithmetic is used.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import comb
from pathlib import Path


def _binomial_weights(n: int, a: int, d: int) -> list[int]:
    """Numerators for Bin(n, a/d), all over the common denominator d**n."""
    if n < 0 or d <= 0 or not 0 <= a <= d:
        raise ValueError("require n >= 0 and 0 <= a <= denominator")
    den = d**n
    if a == 0:
        return [den] + [0] * n
    if a == d:
        return [0] * n + [den]
    weights = [(d - a) ** n]
    term = weights[0]
    for k in range(n):
        numerator = term * (n - k) * a
        divisor = (k + 1) * (d - a)
        if numerator % divisor:
            raise ArithmeticError("nonintegral binomial recurrence")
        term = numerator // divisor
        weights.append(term)
    return weights


def _tail_is_at_most(n: int, successes: int, a: int, d: int,
                      alpha_num: int, alpha_den: int, upper: bool) -> bool:
    weights = _binomial_weights(n, a, d)
    tail_num = sum(weights[successes:]) if upper else sum(weights[:successes + 1])
    return tail_num * alpha_den <= alpha_num * (d**n)


def cp_grid_bounds(successes: int, n: int, alpha_tail: Fraction,
                   denominator: int = 100_000) -> tuple[Fraction, Fraction]:
    """Outward-rounded two-sided Clopper-Pearson interval on a rational grid.

    The lower endpoint is the greatest grid point whose upper binomial tail at
    `successes` is <= alpha_tail. The upper endpoint is the least grid point
    whose lower tail through `successes` is <= alpha_tail.
    """
    if n <= 0 or not 0 <= successes <= n:
        raise ValueError("require n > 0 and 0 <= successes <= n")
    if not 0 < alpha_tail < 1:
        raise ValueError("alpha_tail must lie strictly between zero and one")
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    an, ad = alpha_tail.numerator, alpha_tail.denominator

    if successes == 0:
        lower = 0
    else:
        lo, hi = 0, denominator
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if _tail_is_at_most(n, successes, mid, denominator, an, ad, upper=True):
                lo = mid
            else:
                hi = mid - 1
        lower = lo

    if successes == n:
        upper = denominator
    else:
        lo, hi = 0, denominator
        while lo < hi:
            mid = (lo + hi) // 2
            if _tail_is_at_most(n, successes, mid, denominator, an, ad, upper=False):
                hi = mid
            else:
                lo = mid + 1
        upper = lo

    return Fraction(lower, denominator), Fraction(upper, denominator)


def simultaneous_roc_bands(data: dict) -> dict:
    """Build Bonferroni-simultaneous FPR/TPR bands for fixed thresholds.

    Data keys: alpha, safe_n, backdoor_n, thresholds[{name, fp, tp}], and
    optional endpoint_denominator. alpha/(4K) is allocated to each tail of
    each of the two rates at each of K operating points.
    """
    alpha = Fraction(str(data["alpha"]))
    safe_n, bad_n = int(data["safe_n"]), int(data["backdoor_n"])
    thresholds = data["thresholds"]
    d = int(data.get("endpoint_denominator", 100_000))
    k = len(thresholds)
    if not 0 < alpha < 1 or safe_n <= 0 or bad_n <= 0 or k <= 0:
        raise ValueError("alpha, both sample sizes, and threshold count must be positive")
    tail = alpha / (4 * k)
    rows = []
    names = set()
    for row in thresholds:
        name, fp, tp = str(row["name"]), int(row["fp"]), int(row["tp"])
        if name in names:
            raise ValueError(f"duplicate threshold name: {name}")
        names.add(name)
        fpr = cp_grid_bounds(fp, safe_n, tail, d)
        tpr = cp_grid_bounds(tp, bad_n, tail, d)
        rows.append({
            "name": name,
            "safe_false_positive_count": fp,
            "safe_sample_size": safe_n,
            "fpr_interval": [str(fpr[0]), str(fpr[1])],
            "backdoor_true_positive_count": tp,
            "backdoor_sample_size": bad_n,
            "tpr_interval": [str(tpr[0]), str(tpr[1])],
        })
    return {
        "method": "two-sided exact binomial tails, Bonferroni over 2 rates x K thresholds",
        "familywise_alpha": str(alpha),
        "per_tail_alpha": str(tail),
        "threshold_count": k,
        "endpoint_grid_denominator": d,
        "thresholds": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("counts", type=Path, help="JSON with held-out counts and predeclared thresholds")
    parser.add_argument("--output", type=Path, help="write JSON output here; otherwise print it")
    args = parser.parse_args()
    result = simultaneous_roc_bands(json.loads(args.counts.read_text()))
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
