"""F6 reference audit policy: precommitted hidden budget allocation.

A fixed set of B audited rounds out of N is sampled once. A false-positive
decision in an earlier audited round DOES NOT spend or cancel a later slot.
This realizes the idealized uniform audit schedule of AuditBudget.lean, *not*
the stronger content-adaptive/red-sees-feedback / imperfect-recall model.

The caller MUST keep scheduled positions, auditor output and timing hidden
from the adversary during the fixed horizon. This module is not a live monitor.
"""
from __future__ import annotations

import secrets
from fractions import Fraction
from math import comb


class AuditPlan:
    def __init__(self, horizon: int, budget: int, rng=None):
        if type(horizon) is not int or not 1 <= horizon <= 100000:
            raise ValueError("bounded positive horizon required")
        if type(budget) is not int or not 0 <= budget <= horizon:
            raise ValueError("budget must lie within horizon")
        rand = rng if rng is not None else secrets.SystemRandom()
        self._slots = frozenset(rand.sample(range(horizon), budget))
        self._horizon, self._budget = horizon, budget
        self._next = 0
        self._decisions = []

    def audit_round(self, round_index: int, verdict: bool = False) -> bool:
        """Trusted-only; never expose the result to the adversary mid-horizon.

        verdict is the monitor's outcome for this round and is *not* used for
        scheduling. Overriding/refunding budget based on verdict could make
        the schedule observable and invalidate the combinatorial bound.
        """
        if type(round_index) is not int or round_index != self._next:
            raise ValueError("out-of-order, duplicate or forged audit round")
        if type(verdict) is not bool:
            raise ValueError("auditor verdict must be a trusted boolean")
        hit = round_index in self._slots
        self._decisions.append((hit, verdict))
        self._next += 1
        return hit

    def completed(self) -> bool:
        return self._next == self._horizon

    def audit_count(self):
        if not self.completed():
            raise ValueError("do not publish schedule details mid-horizon")
        return sum(1 for hit, _ in self._decisions if hit)


def ideal_miss_probability(horizon: int, budget: int, attacks: int) -> Fraction:
    """Fixed attack-round set, uniform hidden auditing, *perfect* capture.

    Exactly C(N-k,B)/C(N,B) when k attack rounds are distinct and chosen
    independently of schedule. This does NOT describe a strategically adaptive
    adversary who observes audit feedback or controls when the horizon ends.
    """
    if any(type(n) is not int for n in (horizon, budget, attacks)):
        raise ValueError("integers required")
    if horizon <= 0 or not 0 <= budget <= horizon or not 0 <= attacks <= horizon:
        raise ValueError("invalid fixed horizon/audit/attack budget")
    return Fraction(comb(horizon - attacks, budget), comb(horizon, budget))
