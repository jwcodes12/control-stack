#!/usr/bin/env python3
"""Consistency checks between numerics/budgeted_audit.py and the Lean statements in
ControlStack/Families/F6/{FlagBudget,SplitAudit}.lean. Exact rational arithmetic; no randomness.

These checks can find a disagreement between the executable model and a Lean closed form. They cannot establish
the Lean theorems (Lean does that) and they say nothing about a real deployment.
"""
import sys
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import budgeted_audit as m  # noqa: E402

CHECKS = []


def check(fn):
    CHECKS.append(fn)
    return fn


GRID = [(N, Bh, Bf, k) for N in (3, 4, 5) for Bh in range(0, 3) for Bf in range(0, 3) for k in (1, 2, 3)
        if Bh <= N and k <= N]
MONS = [(Fr(1, 2), Fr(1, 4)), (Fr(1, 3), Fr(0)), (Fr(1), Fr(1, 2)), (Fr(0), Fr(1, 5))]


@check
def lean_numbers():
    """Numbers stated in Lean: AuditBudget.choose_*, SplitAudit.split_example, SplitAudit.hidden_one_step."""
    assert m.hyp(100, 10, 5) == Fr(10104934117421, 17310309456440)
    assert m.product_pre_bound(100, 10, 5, Fr(1, 2)) == Fr(10104934117421, 553929902606080)
    for N in range(1, 30):
        for Bh in range(0, N + 1):
            assert m.hyp(N, Bh, 1) == 1 - Fr(Bh, N)


@check
def bin_tail_is_binomial():
    """FlagBudget.binTail (recursion) is the binomial tail."""
    for alpha in (Fr(0), Fr(1, 7), Fr(1, 2), Fr(1)):
        for n in range(0, 9):
            for Bf in range(0, 6):
                assert m.bin_tail(alpha, Bf, n) == m.bin_tail_direct(alpha, Bf, n), (alpha, n, Bf)
    a = Fr(3, 10)
    assert m.bin_tail(a, 1, 2) == a + (1 - a) * a  # second conjunct of exhaustion_witness


@check
def lean_witnesses():
    """The three kernel witnesses of SplitAudit.lean, recomputed."""
    for a in (Fr(0), Fr(1, 10), Fr(1, 2), Fr(1)):
        # exhaustion_witness: recall 1, false-positive rate a, Bf = 1, last-round attacker succeeds w.p. a
        assert m.value(2, 0, 1, 1, m.attack_at(1), m.iid_monitor(1, a)) == a
        assert m.optimal(2, 0, 1, 1, m.iid_monitor(1, a), m.ev_pre) == 0  # pre-exhaustion bound (1-1)^1
    # average_recall_witness
    assert m.value(2, 0, 2, 1, m.spread_attacker, m.class_monitor) == Fr(1, 2)
    assert m.value(2, 0, 2, 1, m.attack_at(1), m.class_monitor) == 1
    assert m.flag_bound(2, 2, 1, Fr(1, 2), Fr(0)) == Fr(1, 2)
    # dependence_witness
    assert m.value(2, 1, 1, 1, m.attack_at(0), m.sched_monitor) == Fr(1, 2)
    assert sum(Fr(1, 2) * m.sched_monitor(S, (), True) for S in m.schedules(2, 1)) == Fr(1, 2)
    assert m.hyp(2, 1, 1) * (1 - Fr(1, 2)) == Fr(1, 4)


@check
def bounds_hold_on_grid():
    """Exact optimum <= each Lean bound whose premises the i.i.d. monitor satisfies."""
    for (N, Bh, Bf, k) in GRID:
        for (rho, alpha) in MONS:
            tau = m.iid_monitor(rho, alpha)
            opt = m.optimal(N, Bh, Bf, k, tau)
            assert opt <= m.hyp(N, Bh, k), ("hidden", N, Bh, Bf, k, rho, alpha)
            assert opt <= m.flag_bound(N, Bf, k, rho, alpha), ("flag", N, Bh, Bf, k, rho, alpha)
            assert opt <= m.product_bound(N, Bh, Bf, k, rho, alpha), ("product", N, Bh, Bf, k, rho, alpha)
            pre = m.optimal(N, Bh, Bf, k, tau, m.ev_pre)
            assert pre <= m.product_pre_bound(N, Bh, k, rho), ("product_pre", N, Bh, Bf, k, rho, alpha)
            assert pre <= opt


@check
def flag_bound_holds_for_known_schedule():
    """split_flag_bound is per schedule: it holds when the attacker knows S; the hidden bound then fails."""
    tau = m.iid_monitor(Fr(1, 2), Fr(1, 4))
    for (N, Bh, Bf, k) in [(4, 1, 1, 2), (5, 2, 1, 2), (5, 2, 2, 3)]:
        S = range(Bh)
        v = m.optimal(N, Bh, Bf, k, tau, known=S)
        assert v <= m.flag_bound(N, Bf, k, Fr(1, 2), Fr(1, 4))
    # observable schedule, no flag audits: the attacker avoids S and always succeeds (AuditBudget.observable_schedule_nogo)
    assert m.optimal(5, 2, 0, 3, tau, known=range(2)) == 1
    assert m.hyp(5, 2, 3) < 1


@check
def product_pre_is_tight_without_false_positives():
    """With no false positives the pre-exhaustion product bound is attained exactly."""
    for (N, Bh, Bf, k, rho) in [(7, 2, 2, 3, Fr(1, 3)), (5, 1, 1, 2, Fr(1, 2)), (6, 2, 3, 2, Fr(1, 4))]:
        v = m.optimal(N, Bh, Bf, k, m.iid_monitor(rho, 0), m.ev_pre) if N <= 6 else \
            m.dp(N, Bh, Bf, k, rho, 0, pre=True)
        assert v == m.product_pre_bound(N, Bh, k, rho), (N, Bh, Bf, k, rho, v)
    assert m.product_pre_bound(7, 2, 3, Fr(1, 3)) == Fr(16, 189)


@check
def exhaustion_beats_the_recall_term():
    """Values found independently by a reviewer's own programme (N=6, Bf=1, k=2, recall 1/2, FP rate 1/4):
    the pre-exhaustion event has value (1/2)^2 but the attacker's real success is far larger."""
    tau = m.iid_monitor(Fr(1, 2), Fr(1, 4))
    assert m.optimal(6, 0, 1, 2, tau, m.ev_pre) == Fr(1, 4)
    assert m.optimal(6, 0, 1, 2, tau) == Fr(781, 1024)
    assert m.optimal(6, 2, 1, 2, tau) == Fr(781, 2560)
    assert Fr(781, 2560) > min(m.hyp(6, 2, 2), Fr(1, 4))  # "min of the two" is false for the total-attack event
    assert Fr(781, 2560) <= m.product_bound(6, 2, 1, 2, Fr(1, 2), Fr(1, 4))


@check
def dp_matches_exhaustive():
    """The reduced-state programme equals exhaustive recursion (both events, optimal and memoryless)."""
    for (N, Bh, Bf, k) in GRID:
        for (rho, alpha) in MONS:
            tau = m.iid_monitor(rho, alpha)
            assert m.dp(N, Bh, Bf, k, rho, alpha) == m.optimal(N, Bh, Bf, k, tau), (N, Bh, Bf, k, rho, alpha)
            assert m.dp(N, Bh, Bf, k, rho, alpha, pre=True) == m.optimal(N, Bh, Bf, k, tau, m.ev_pre)
    for (N, Bh, Bf, k) in [(4, 1, 1, 2), (5, 2, 1, 2), (5, 1, 2, 1)]:
        for beta in (Fr(1, 3), Fr(1, 2)):
            tau = m.iid_monitor(Fr(1, 2), Fr(1, 4))
            assert m.dp(N, Bh, Bf, k, Fr(1, 2), Fr(1, 4), beta=beta) == m.value(N, Bh, Bf, k, m.memoryless(beta, k), tau)


@check
def prefix_event_has_the_same_optimum():
    """NOT proved in Lean: "k attacks released before the first catch" has the same supremum over attackers as
    "at least k attacks, never caught" (an attacker can stop after k; a non-attack is never caught)."""
    for (N, Bh, Bf, k), (rho, alpha) in product(GRID, MONS[:2]):
        tau = m.iid_monitor(rho, alpha)
        assert m.optimal(N, Bh, Bf, k, tau, m.ev_prefix) == m.optimal(N, Bh, Bf, k, tau), (N, Bh, Bf, k)


@check
def adaptive_beats_memoryless():
    """The optimal attacker is at least as good as every memoryless one, strictly so when flags can exhaust."""
    best = max(m.dp(6, 0, 1, 2, Fr(1, 2), Fr(1, 4), beta=Fr(i, 20)) for i in range(0, 21))
    assert best < m.dp(6, 0, 1, 2, Fr(1, 2), Fr(1, 4))


@check
def late_blind_attacker():
    """The attacker who attacks in the last k rounds without looking at any flag: the programme's `late` mode equals
    the explicit strategy, and on these instances it already achieves the optimum."""
    for (N, Bh, Bf, k) in [(5, 0, 1, 2), (5, 1, 1, 2), (6, 2, 2, 3)]:
        rho, alpha = Fr(1, 2), Fr(1, 4)
        tau = m.iid_monitor(rho, alpha)
        v = m.value(N, Bh, Bf, k, m.late_attacker(N, k), tau)
        assert v == m.dp(N, Bh, Bf, k, rho, alpha, late=True)
        assert v == m.optimal(N, Bh, Bf, k, tau)


@check
def results_file_is_current():
    assert m.main(["--check"]) == 0


def main():
    failed = 0
    for fn in CHECKS:
        try:
            fn()
            print(f"ok   {fn.__name__}")
        except AssertionError as e:
            failed += 1
            print(f"FAIL {fn.__name__}: {e}")
    print(f"{len(CHECKS) - failed}/{len(CHECKS)} checks passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
