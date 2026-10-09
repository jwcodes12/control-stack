#!/usr/bin/env python3
"""Tests for tools/measured.py (stdlib unittest; no model calls). Run: python3 -m unittest tools/test_measured.py"""
import math
import os
import sys
import tempfile
import unittest
from fractions import Fraction

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import measured as M  # noqa: E402


def tail_direct(k, n, r):
    r = Fraction(r)
    return sum(math.comb(n, i) * r ** i * (1 - r) ** (n - i) for i in range(k, n + 1))


class Tail(unittest.TestCase):
    def test_exact_matches_direct_sum(self):
        for n in (1, 2, 5, 13, 40):
            for k in range(0, n + 2):
                for r in (Fraction(0), Fraction(1, 3), Fraction(9, 10), Fraction(123457, 1000000), Fraction(1)):
                    num, den = M.tail_exact(k, n, r)
                    self.assertEqual(Fraction(num, den), tail_direct(k, n, r), (k, n, r))

    def test_float_agrees(self):
        for k, n, p in ((3, 10, 0.2), (190, 200, 0.9), (5, 5, 0.5), (0, 7, 0.3), (8, 7, 0.3)):
            exact = float(tail_direct(k, n, Fraction(p))) if k <= n else 0.0
            self.assertAlmostEqual(M.binom_sf_float(k, n, p), exact, places=9)


class Bound(unittest.TestCase):
    def test_all_successes_closed_form(self):
        r0, t = M.certified_lower(5, 5, 0.05)
        self.assertLessEqual(float(r0), 0.05 ** (1 / 5))
        self.assertGreater(float(r0), 0.05 ** (1 / 5) - 2e-6)
        self.assertLessEqual(t, 0.05)

    def test_tight_and_valid(self):
        for k, n, d in ((3, 10, 0.05), (16, 16, 0.05), (2047, 20000, 0.01), (64, 64, 0.1)):
            r0, _ = M.certified_lower(k, n, d)
            num, den = M.tail_exact(k, n, r0)
            self.assertLessEqual(Fraction(num, den), Fraction(d).limit_denominator(10 ** 9))
            nxt = r0 + Fraction(1, 10 ** M.DIGITS)
            num, den = M.tail_exact(k, n, nxt)
            self.assertGreater(Fraction(num, den), Fraction(d).limit_denominator(10 ** 9))   # rounding loses < 1e-6

    def test_matches_lean_instance_tail_200_190(self):
        # Measured.tail_200_190: P_{9/10}(S >= 190) <= 1/100, so r_low(190, 200, 0.01) >= 9/10
        r0, _ = M.certified_lower(190, 200, 0.01)
        self.assertGreaterEqual(r0, Fraction(9, 10))

    def test_zero_successes(self):
        self.assertEqual(M.certified_lower(0, 10, 0.05)[0], 0)


class Repo(unittest.TestCase):
    def test_ledger(self):
        led = M.read_ledger()
        if not led:
            self.skipTest("no ASSURANCE-LEDGER.md")
        self.assertEqual(led["honest_usefulness"]["kind"], "measurement")
        self.assertIn("SC-26", led["honest_usefulness"]["scenarios"])

    def test_collect_rows_are_sourced(self):
        rows, notes = M.collect(0.05, M.read_ledger())
        self.assertTrue(rows)
        for r in rows:
            self.assertEqual(M.sha256(os.path.join(M.REPO, r["source"])), r["sha256"])
            self.assertTrue(0 <= r["k"] <= r["n"])
            self.assertLessEqual(r["r_low"], r["point"] + 1e-12)
            self.assertTrue(r["caveat"])
        only, _ = M.collect(0.05, M.read_ledger(), measurement_only=True)
        self.assertTrue(all(r["kind"] == "measurement" for r in only))

    def test_lean_snippet(self):
        rows = [{"premise": "p", "scenario": "SC-01", "label": "x", "k": 16, "n": 16, "r_low_rational": "1/2",
                 "tail_at_r_low": 1.5e-5, "source": "s", "sha256": "0" * 64, "caveat": "c"}]
        old = M.MEASURED_LEAN
        try:
            M.MEASURED_LEAN = "/nonexistent/Measured.lean"
            self.assertIsNone(M.lean_snippet(rows, 0.05)[0])
            with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
                f.write("namespace ControlStack.Measured\nnoncomputable def tailP\ndef cnt\ndef wB\n")
            M.MEASURED_LEAN = f.name
            snip, why = M.lean_snippet(rows, 0.05)
            self.assertIsNone(snip)
            self.assertIn("cp_threshold", why)
            with open(f.name, "a") as g:
                g.write("theorem cp_threshold\n")
            snip, why = M.lean_snippet(rows, 0.05)
            self.assertIn("cp_threshold 16 16 (1/2 : ℝ) (1/20 : ℝ)", snip)
            self.assertIn("import ControlStack.Core.Measured", snip)
            os.unlink(f.name)
        finally:
            M.MEASURED_LEAN = old


if __name__ == "__main__":
    unittest.main()
