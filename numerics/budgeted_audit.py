#!/usr/bin/env python3
"""Executable model of the M1 flagship: budgeted auditing against an adaptive attacker.

It instantiates the round kernel `ControlStack.SplitAudit.splitK` (ControlStack/Families/F6/SplitAudit.lean):
N rounds; the attacker picks an attack bit from the visible history (its own bits, every flag, every catch); the
monitor flags; an attack is caught iff the round is in the hidden reserved schedule S (Bh uniformly random rounds)
or it is flagged while fewer than Bf earlier rounds were flagged.

What this file is: exact rational arithmetic on that model. It computes the best an attacker can do, evaluates
named attackers, and compares the results with the closed forms proved in Lean.
What it is not: evidence about any real monitor, attacker or deployment, and not a proof. Agreement between this
file and the Lean statements is executable-model agreement only; nothing here links Lean to a runtime.

Usage:
  python3 numerics/budgeted_audit.py            # print the tables
  python3 numerics/budgeted_audit.py --write    # regenerate numerics/budgeted_audit/results.json
  python3 numerics/budgeted_audit.py --check    # fail if results.json is stale
  python3 numerics/test_budgeted_audit.py       # consistency checks against the Lean statements
"""
import json
import sys
from fractions import Fraction as Fr
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path

RESULTS = Path(__file__).resolve().parent / "budgeted_audit" / "results.json"

# ---------------------------------------------------------------------------------------------------------------
# Closed forms proved in Lean
# ---------------------------------------------------------------------------------------------------------------


def hyp(N, Bh, k):
    """C(N-k,Bh)/C(N,Bh), natural subtraction as in Lean. `SplitAudit.split_hidden_bound`."""
    return Fr(comb(max(N - k, 0), Bh), comb(N, Bh))


def bin_tail(alpha, Bf, n, j=0):
    """P(a flag count now at j reaches Bf within n rounds of rate alpha). Mirrors `FlagBudget.binTail`."""
    row = [1 if Bf <= i else 0 for i in range(j, j + n + 2)]
    for _ in range(n):
        row = [1 if Bf <= j + i else alpha * row[i + 1] + (1 - alpha) * row[i] for i in range(len(row) - 1)]
    return row[0]


def bin_tail_direct(alpha, Bf, n):
    """The same quantity as a binomial sum: P(Binomial(n, alpha) >= Bf)."""
    return sum(comb(n, i) * alpha**i * (1 - alpha) ** (n - i) for i in range(Bf, n + 1))


def flag_bound(N, Bf, k, rho, alpha):
    """(1-rho)^k + P(Bin(N,alpha) >= Bf). `SplitAudit.split_flag_bound` (any schedule, even a known one)."""
    return (1 - rho) ** k + bin_tail(alpha, Bf, N)


def product_bound(N, Bh, Bf, k, rho, alpha):
    """C/C * (1-rho)^k + P(Bin(N,alpha) >= Bf). `SplitAudit.split_product_bound` (S-independent flags)."""
    return hyp(N, Bh, k) * (1 - rho) ** k + bin_tail(alpha, Bf, N)


def product_pre_bound(N, Bh, k, rho):
    """C/C * (1-rho)^k for the pre-exhaustion event. `SplitAudit.split_product_pre`."""
    return hyp(N, Bh, k) * (1 - rho) ** k


# ---------------------------------------------------------------------------------------------------------------
# The model: transcripts, events, monitors
# ---------------------------------------------------------------------------------------------------------------
# A transcript g is a tuple of rounds (attack, flag, caught).


def flag_count(g):
    return sum(1 for (_, f, _) in g if f)


def catch_rule(Bf, S, g, a, f):
    """`SplitAudit.catchRule`."""
    return a and (len(g) in S or (f and flag_count(g) < Bf))


def live(g):
    return not any(c for (_, _, c) in g)


def attacks(g):
    return sum(1 for (a, _, _) in g if a)


def pre_attacks(Bf, g):
    """`FlagBudget.preAtt`: attacks made while fewer than Bf earlier rounds were flagged."""
    m, j = 0, 0
    for (a, f, _) in g:
        if a and j < Bf:
            m += 1
        if f:
            j += 1
    return m


def ev_tot(k, Bf):
    """`FlagBudget.totSucc`: at least k attacks and never caught."""
    return lambda g: 1 if live(g) and attacks(g) >= k else 0


def ev_pre(k, Bf):
    """`FlagBudget.preSucc`: additionally at least k of the attacks were pre-exhaustion."""
    return lambda g: 1 if live(g) and attacks(g) >= k and pre_attacks(Bf, g) >= k else 0


def ev_prefix(k, Bf):
    """NOT a Lean event: k attacks were released before the first catch (harm done even if caught later)."""

    def ev(g):
        n = 0
        for (a, _, c) in g:
            if c:
                return 0
            if a:
                n += 1
                if n >= k:
                    return 1
        return 0

    return ev


def iid_monitor(rho, alpha):
    """Flags an attack with probability rho and a non-attack with probability alpha, whatever the history."""
    return lambda S, g, a: rho if a else alpha


def class_monitor(S, g, a):
    """`SplitAudit.classMonitor`: flags an attack in round 0, misses later ones; no false positives."""
    return 1 if (a and len(g) == 0) else 0


def sched_monitor(S, g, a):
    """`SplitAudit.schedMonitor`: flags an attack exactly when the round is reserved."""
    return 1 if (a and len(g) in S) else 0


def schedules(N, Bh):
    return [frozenset(c) for c in combinations(range(N), Bh)]


# ---------------------------------------------------------------------------------------------------------------
# Exact values by exhaustive recursion over visible histories (no state reduction)
# ---------------------------------------------------------------------------------------------------------------


def _children(Bf, scheds, tau, g, w, a):
    """All (round output, schedule weights) reachable when the attack bit is a."""
    out = []
    for f in (False, True):
        for c in (False, True):
            w2 = []
            for S, ws in zip(scheds, w):
                if ws == 0 or c != catch_rule(Bf, S, g, a, f):
                    w2.append(Fr(0))
                    continue
                pf = Fr(tau(S, g, a))
                w2.append(ws * (pf if f else 1 - pf))
            if any(w2):
                out.append(((a, f, c), tuple(w2)))
    return out


def optimal(N, Bh, Bf, k, tau, event=ev_tot, known=None):
    """Supremum over attackers (any function of the visible history) of P(event), exactly.

    Backward induction over visible histories carrying the unnormalised joint weight of each schedule; this is
    exact for a perfect-recall decision problem. `known`: a single schedule the attacker knows (prior = point mass).
    """
    scheds = [frozenset(known)] if known is not None else schedules(N, Bh)
    ev = event(k, Bf)

    def rec(g, w):
        if len(g) == N:
            return ev(g) * sum(w)
        return max(sum(rec(g + (o,), w2) for (o, w2) in _children(Bf, scheds, tau, g, w, a)) for a in (False, True))

    return rec((), tuple(Fr(1, len(scheds)) for _ in scheds))


def value(N, Bh, Bf, k, sigma, tau, event=ev_tot, known=None):
    """P(event) for a given attacker sigma(g) = probability of attacking at visible history g, exactly."""
    scheds = [frozenset(known)] if known is not None else schedules(N, Bh)
    ev = event(k, Bf)

    def rec(g, w):
        if len(g) == N:
            return ev(g) * sum(w)
        p = Fr(sigma(g))
        tot = Fr(0)
        for a, pa in ((False, 1 - p), (True, p)):
            if pa:
                tot += pa * sum(rec(g + (o,), w2) for (o, w2) in _children(Bf, scheds, tau, g, w, a))
        return tot

    return rec((), tuple(Fr(1, len(scheds)) for _ in scheds))


# named attackers -------------------------------------------------------------------------------------------------


def attack_at(r):
    """`SplitAudit.attackAt`: attacks exactly in round r, ignoring everything it sees."""
    return lambda g: 1 if len(g) == r else 0


def spread_attacker(g):
    """`SplitAudit.spreadAttacker` (N = 2): round 0 with probability 1/2, otherwise round 1."""
    if len(g) == 0:
        return Fr(1, 2)
    return 0 if g[0][0] else 1


def late_attacker(N, k):
    """Attacks in the last k rounds. Sees nothing; exploits only that false positives accumulate."""
    return lambda g: 1 if len(g) >= N - k else 0


def memoryless(beta, k):
    """Attacks with probability beta in each round until it has attacked k times (the usual red-team model)."""
    return lambda g: beta if attacks(g) < k else 0


# ---------------------------------------------------------------------------------------------------------------
# Reduced-state dynamic programme for the i.i.d. monitor (validated against `optimal` in the tests)
# ---------------------------------------------------------------------------------------------------------------


def dp(N, Bh, Bf, k, rho, alpha, beta=None, pre=False, num=Fr, late=False):
    """Value against the i.i.d. monitor. beta=None: optimal attacker. beta=x: memoryless attacker of rate x.
    late=True: the blind attacker who attacks in the last k rounds and never looks at a flag.

    State after i rounds on a live path: u attacks so far (the attacker stops at k: further attacks cannot help),
    m of them pre-exhaustion, j flags so far (capped at Bf). On a live path the posterior of S is uniform over
    Bh-subsets of the N - u rounds not attacked, so the current round is reserved with probability Bh/(N - u).
    """
    rho, alpha = num(rho), num(alpha)
    one, zero = num(1), num(0)
    M = k if pre else 0  # the pre-exhaustion count is only tracked when the event needs it
    V = [[[one if (u >= k and (not pre or m >= k)) else zero for _ in range(Bf + 1)] for m in range(M + 1)]
         for u in range(k + 1)]
    for t in range(N):  # t = number of rounds still to come after this one
        W = [[[zero] * (Bf + 1) for _ in range(M + 1)] for _ in range(k + 1)]
        for u in range(k + 1):
            for m in range(min(u, M) + 1):
                for j in range(Bf + 1):
                    j1 = min(j + 1, Bf)
                    wait = alpha * V[u][m][j1] + (1 - alpha) * V[u][m][j]
                    if u >= k:
                        W[u][m][j] = wait
                        continue
                    free = N - u
                    not_reserved = (num(free - Bh) / num(free)) if free > Bh else zero
                    if j < Bf:
                        att = not_reserved * (1 - rho) * V[u + 1][min(m + 1, M)][j]
                    else:
                        att = not_reserved * V[u + 1][m][Bf]
                    if late:
                        W[u][m][j] = att if t < k else wait
                    elif beta is None:
                        W[u][m][j] = max(wait, att)
                    else:
                        W[u][m][j] = beta * att + (1 - beta) * wait
        V = W
    return V[0][0][0]


def best_memoryless(N, Bh, Bf, k, rho, alpha, grid=24):
    """Best memoryless rate on a geometric grid from 1/N to 1 (floats): the usual red-team model, for comparison
    with the optimum. A grid maximum is a lower bound on the best memoryless attacker."""
    best = (0.0, 0.0)
    for i in range(grid + 1):
        b = (1.0 / N) ** (1 - i / grid)
        v = dp(N, Bh, Bf, k, rho, alpha, beta=b, num=float)
        if v > best[0]:
            best = (v, b)
    return best


# ---------------------------------------------------------------------------------------------------------------
# Tables
# ---------------------------------------------------------------------------------------------------------------


def _s(x):
    return str(x) if isinstance(x, Fr) else round(float(x), 6)


def table_small():
    """Exact optimal attacker against the Lean bounds, N = 6, recall 1/2, false-positive rate 1/4."""
    N, rho, alpha = 6, Fr(1, 2), Fr(1, 4)
    tau = iid_monitor(rho, alpha)
    rows = []
    for (Bh, Bf) in ((2, 0), (0, 2), (1, 1), (2, 2)):
        for k in (1, 2, 3):
            opt = optimal(N, Bh, Bf, k, tau)
            rows.append({
                "N": N, "Bh": Bh, "Bf": Bf, "k": k,
                "optimal": _s(opt),
                "optimal_float": _s(float(opt)),
                "late_attacker": _s(value(N, Bh, Bf, k, late_attacker(N, k), tau)),
                "bound_hidden": _s(hyp(N, Bh, k)),
                "bound_flag": _s(min(Fr(1), flag_bound(N, Bf, k, rho, alpha))),
                "bound_product": _s(min(Fr(1), product_bound(N, Bh, Bf, k, rho, alpha))),
                "optimal_pre_event": _s(optimal(N, Bh, Bf, k, tau, ev_pre)),
                "bound_product_pre": _s(product_pre_bound(N, Bh, k, rho)),
            })
    return rows


def table_regimes():
    """N = 1000, 2% total audit budget: the hidden-schedule and flag mechanisms per number of attack steps."""
    N, B, rho = 1000, 20, 0.5
    rows = []
    for k in (1, 2, 5, 10, 20, 50, 115):
        rows.append({
            "k": k,
            "hidden_Bh20": _s(float(hyp(N, B, k))),
            "flag_recall_term_rho0.5": _s((1 - rho) ** k),
            "product_Bh10": _s(float(hyp(N, 10, k)) * (1 - rho) ** k),
        })
    return rows


def table_exhaustion():
    """P(Binomial(N, alpha) >= Bf): the exhaustion term, N = 1000."""
    N = 1000
    rows = []
    for Bf in (10, 20, 30):
        for alpha in (0.005, 0.01, 0.015, 0.02, 0.03):
            rows.append({"Bf": Bf, "alpha": alpha, "expected_false_positives": _s(N * alpha),
                         "P_exhaustion": _s(bin_tail(alpha, Bf, N))})
    return rows


def table_split():
    """N = 1000, total budget 20, k = 5, recall 0.5, false-positive rate 0.01: every split of the budget."""
    N, B, k, rho, alpha = 1000, 20, 5, 0.5, 0.01
    rows = []
    for Bh in range(0, B + 1, 2):
        Bf = B - Bh
        bm, beta = best_memoryless(N, Bh, Bf, k, rho, alpha)
        rows.append({
            "Bh": Bh, "Bf": Bf,
            "optimal_attacker": _s(dp(N, Bh, Bf, k, rho, alpha, num=float)),
            "late_blind_attacker": _s(dp(N, Bh, Bf, k, rho, alpha, num=float, late=True)),
            "best_memoryless": _s(bm), "best_memoryless_rate": _s(beta),
            "bound_product": _s(min(1.0, float(hyp(N, Bh, k)) * (1 - rho) ** k + bin_tail(alpha, Bf, N))),
            "P_exhaustion": _s(bin_tail(alpha, Bf, N)),
        })
    return rows


def table_calibrated():
    """Single-step attacks (k = 1), N = 1000, no reserved audits, flag budget 20 with the false-positive rate set
    so that the expected number of false positives equals the budget (alpha = Bf/N), and with slack."""
    N, Bf, k = 1000, 20, 1
    rows = []
    for alpha in (0.02, 0.015, 0.01):
        for rho in (0.5, 0.8, 0.95):
            bm, beta = best_memoryless(N, 0, Bf, k, rho, alpha)
            rows.append({
                "alpha": alpha, "rho": rho,
                "optimal_attacker": _s(dp(N, 0, Bf, k, rho, alpha, num=float)),
                "late_blind_attacker": _s(dp(N, 0, Bf, k, rho, alpha, num=float, late=True)),
                "best_memoryless": _s(bm),
                "recall_term": _s(1 - rho),
                "P_exhaustion": _s(bin_tail(alpha, Bf, N)),
                "bound_flag": _s(min(1.0, (1 - rho) + bin_tail(alpha, Bf, N))),
            })
    return rows


def results():
    return {
        "note": "Executable-model values for numerics/budgeted_audit.py. Fractions are exact; decimals are floats "
                "rounded to 6 places. Not Lean-checked; not evidence about any real monitor or attacker.",
        "small_exact_N6_rho_1/2_alpha_1/4": table_small(),
        "regimes_N1000": table_regimes(),
        "exhaustion_N1000": table_exhaustion(),
        "split_N1000_B20_k5_rho0.5_alpha0.01": table_split(),
        "calibrated_N1000_Bf20_k1": table_calibrated(),
    }


def main(argv):
    res = results()
    text = json.dumps(res, indent=1) + "\n"
    if "--write" in argv:
        RESULTS.parent.mkdir(exist_ok=True)
        RESULTS.write_text(text)
        print(f"wrote {RESULTS}")
        return 0
    if "--check" in argv:
        if not RESULTS.exists() or RESULTS.read_text() != text:
            print("numerics/budgeted_audit/results.json is stale; run with --write")
            return 1
        print("results.json reproduced")
        return 0
    for name, rows in res.items():
        if name == "note":
            continue
        print(f"\n## {name}")
        cols = list(rows[0])
        print(" | ".join(cols))
        for r in rows:
            print(" | ".join(str(r[c]) for c in cols))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
