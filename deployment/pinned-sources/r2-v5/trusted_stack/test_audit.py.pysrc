import itertools
import math
import random
import unittest
from fractions import Fraction
from trusted_stack.audit import AuditPlan, ideal_miss_probability


class AuditPlanTests(unittest.TestCase):
    def test_ideal_uniform_combination_exact(self):
        for n in range(1, 9):
            for b in range(n + 1):
                for k in range(n + 1):
                    attacking = frozenset(range(k))
                    schedules = [frozenset(s) for s in itertools.combinations(range(n), b)]
                    actual = sum(1 for slots in schedules if slots.isdisjoint(attacking))
                    self.assertEqual(Fraction(actual, len(schedules)),
                                     ideal_miss_probability(n, b, k))

    def test_false_positives_never_consume_future_reserved_slots(self):
        a = AuditPlan(40, 8, random.Random(17))
        b = AuditPlan(40, 8, random.Random(17))
        hits_a = [a.audit_round(i, verdict=True) for i in range(40)]
        hits_b = [b.audit_round(i, verdict=False) for i in range(40)]
        self.assertEqual(hits_a, hits_b)
        self.assertEqual(a.audit_count(), 8)
        self.assertEqual(b.audit_count(), 8)

    def test_out_of_order_and_duplicate_rounds_refused(self):
        plan = AuditPlan(5, 2, random.Random(20))
        with self.assertRaises(ValueError):
            plan.audit_round(1)
        plan.audit_round(0)
        with self.assertRaises(ValueError):
            plan.audit_round(0)
        with self.assertRaises(ValueError):
            plan.audit_count()

    def test_trust_and_configuration_boundaries(self):
        for params in ((0, 0), (2, 3), (True, 0), (2, True), (5, -1)):
            with self.subTest(params=params), self.assertRaises(ValueError):
                AuditPlan(*params)
        self.assertEqual(ideal_miss_probability(10, 10, 1), Fraction(0))
        self.assertEqual(ideal_miss_probability(10, 0, 5), Fraction(1))


if __name__ == "__main__":
    unittest.main()
