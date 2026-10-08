"""Regression values for tools/ctrlcert.py (each matches a Lean-certified number in ControlStack/)."""
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ctrlcert  # noqa: E402


class CtrlCert(unittest.TestCase):
    def test_hypergeometric_matches_audit_budget(self):
        # AuditBudget.budget_example: choose 95 10 / choose 100 10
        self.assertEqual(ctrlcert.hyper(100, 10, 5), F(10104934117421, 17310309456440))

    def test_cp_lower_matches_cache_receipt(self):
        # gateway/scenario/results/local-cache.json: 64/64 -> 95427/100000
        self.assertEqual(ctrlcert.cp_lower(64, 64, F(1, 20)), F(95427, 100000))

    def test_cp_lower_matches_usefulness_endpoint(self):
        # ScenarioAUsefulness.endpoint64 at tail 1/80: 93382/100000
        self.assertEqual(ctrlcert.cp_lower(64, 64, F(1, 80)), F(93382, 100000))

    def test_one_bit_leak_exact_below_bound(self):
        exact = ctrlcert.one_bit_leak_exact(100, 10, 5)
        self.assertLess(ctrlcert.hyper(100, 10, 5), exact)
        self.assertLess(exact, 2 * ctrlcert.hyper(100, 10, 5))


if __name__ == "__main__":
    unittest.main()
