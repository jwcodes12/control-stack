#!/usr/bin/env python3
"""Unit tests for the SC-21 sampling validation harness (fast; no evidence)."""
import math
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pipeline as PL  # noqa: E402
import stats as ST  # noqa: E402
import run_sampling as R  # noqa: E402
from tasks import task  # noqa: E402


class ExactValues(unittest.TestCase):
    def test_matches_lean_example(self):
        # EvalIntegrityAdaptive.sc21_adaptive_example: N = 100, B = 10, k = 5
        self.assertEqual(ST.bound_hidden(100, 10, 5), Fraction(10104934117421, 17310309456440))

    def test_hypmiss_r1_is_hidden_bound(self):
        for k in (1, 3, 5):
            self.assertEqual(ST.hyp_miss(100, 10, k, 1), ST.bound_hidden(100, 10, k))

    def test_hypmiss_r0_is_one(self):
        self.assertEqual(ST.hyp_miss(100, 10, 3, 0), 1)

    def test_hypmiss_monotone_in_r(self):
        self.assertLess(ST.hyp_miss(100, 10, 3, Fraction(3, 4)), ST.hyp_miss(100, 10, 3, Fraction(1, 2)))


class Binomial(unittest.TestCase):
    def direct_sf(self, x, n, p):
        return sum(math.comb(n, j) * p ** j * (1 - p) ** (n - j) for j in range(x, n + 1))

    def test_sf_against_direct_sum(self):
        for x, n, p in ((3, 10, 0.3), (0, 5, 0.5), (50, 60, 0.9), (17, 40, 0.584)):
            self.assertAlmostEqual(ST.binom_sf(x, n, p), self.direct_sf(x, n, p), places=10)

    def test_clopper_pearson_known(self):
        lo, hi = ST.clopper_pearson(0, 16, 0.95)
        self.assertEqual(lo, 0.0)
        self.assertAlmostEqual(hi, 0.2059, places=3)
        lo, hi = ST.clopper_pearson(4, 4, 0.95)
        self.assertAlmostEqual(lo, 0.3976, places=3)


class Pipeline(unittest.TestCase):
    def test_tasks_deterministic(self):
        self.assertTrue(PL.determinism_check(100))
        self.assertEqual(task(7), task(7))

    def test_fixed_attacks_exactly_k_and_no_violation(self):
        res = PL.run_config(100, 10, 3, 1, "fixed", 300, "unit")
        self.assertEqual(res["reached_k"], 300)
        self.assertEqual(res["detection_violations"], 0)

    def test_policies_reach_k(self):
        for adv in ("pace", "burst", "leak"):
            res = PL.run_config(100, 10, 5, 1, adv, 200, "unit", q=0.5)
            self.assertEqual(res["reached_k"], 200, adv)

    def test_full_leak_always_survives(self):
        # observable_sample_nogo: with the sample fully leaked, k <= N - B corruptions all avoid it
        res = PL.run_config(100, 10, 5, 1, "leak", 300, "unit", q=1.0)
        self.assertEqual(res["hidden_success"], 300)

    def test_mutations_caught(self):
        nore = PL.run_config(100, 10, 3, 1, "fixed", 300, "unit", mutation="no_reexec")
        self.assertGreater(nore["detection_violations"], 0)
        bias = PL.run_config(100, 10, 3, 1, "fixed", 300, "unit", mutation="biased_sample")
        self.assertFalse(PL.uniformity_check(bias["inclusion"], 300, 100, 10, R.Z_CRIT)[0])
        self.assertFalse(PL.determinism_check(100, mutation="nondet_task", repeats=50))

    def test_streams_independent_of_adversary(self):
        # the hidden sample stream does not depend on the agent's stream (separate seeds per stream)
        a = PL.streams("s", "c")
        self.assertNotEqual(a["agent"].random(), a["sample"].random())


class Gates(unittest.TestCase):
    def test_evidence_refused_without_env(self):
        class A:
            out = R.EVIDENCE_DIR / "run-x"
            seed = R.EVIDENCE_SEED
            trials = R.EVIDENCE_TRIALS
        self.assertIsNotNone(R.evidence_refusal(A()))


if __name__ == "__main__":
    unittest.main()
