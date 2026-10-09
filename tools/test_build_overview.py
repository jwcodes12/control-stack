#!/usr/bin/env python3
"""Tests for tools/build_overview.py (stdlib unittest). Run: python3 tools/test_build_overview.py"""
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import build_overview as B  # noqa: E402

LEAN = '''def Root.name : Root → String
  | .kernelMediation => "kernel_mediation"
  | .measuredRates => "measured_rates (residual)"

theorem scenario_roots_table : scenarios.map (fun s => (s.1, scenarioRoots s.1)) =
      [(1, [.kernelMediation, .measuredRates]),
       (26, [.measuredRates])] := by
  decide
'''


def T(name, path="ControlStack/X.lean"):
    return {"name": name, "path": path}


def fake_measured(delta, ledger, measurement_only=False):
    return [{"premise": "honest_usefulness", "scenario": "SC-01", "ledger_member": True, "label": "x | y", "k": 5,
             "n": 5, "r_low": 0.5493, "caveat": "c"}], ["note"]


class Rules(unittest.TestCase):
    def test_strongest_order(self):
        m = {"theorems": [T("A.first"), T("A.sc01_safe"), T("A.concrete_safe"), T("A.sc01_safe_authenticated")]}
        self.assertEqual(B.strongest(m)["name"], "A.sc01_safe_authenticated")
        m["theorems"].pop()
        self.assertEqual(B.strongest(m)["name"], "A.concrete_safe")
        m["theorems"].pop()
        self.assertEqual(B.strongest(m)["name"], "A.sc01_safe")
        self.assertEqual(B.strongest({"theorems": [T("A.foo")]})["name"], "A.foo")
        self.assertIsNone(B.strongest({"theorems": []}))
        self.assertTrue(B.is_refinement(T("A.x", "ControlStack/Scenarios/SC26Refinement.lean")))

    def test_open_premise(self):
        rows = [{"id": "a", "kind": "k", "scenarios": ["SC-01"], "tested_in": ["SC-01"], "leverage": 20},
                {"id": "b", "kind": "k", "scenarios": ["SC-01"], "tested_in": [], "leverage": 3},
                {"id": "c", "kind": "k", "scenarios": ["SC-01"], "tested_in": [], "leverage": 9}]
        self.assertEqual(B.open_premise("SC-01", rows)["id"], "c")
        self.assertIsNone(B.open_premise("SC-02", rows))

    def test_roots(self):
        self.assertEqual(B.roots_from_text(LEAN), {1: ["kernelMediation", "measuredRates"], 26: ["measuredRates"]})
        names = B.root_names(LEAN)
        self.assertEqual(B.fmt_roots(["kernelMediation", "measuredRates"], names), "kernel_mediation, measured_rates*")
        self.assertEqual(B.roots_from_text("nothing"), {})

    def test_scope_dedupe(self):
        ms = {"SC-01": {"scope": "Lean only. Not: GPUs, multiple gates. Runtime: x."},
              "SC-02": {"scope": "Not: multiple gates; kernel exploits."},
              "SC-03": {"scope": "Semantic, unformalised: label correctness."}}
        lim = B.scope_limits(ms)
        self.assertEqual(lim[0], ("multiple gates", ["SC-01", "SC-02"]))
        self.assertIn(("label correctness", ["SC-03"]), lim)
        self.assertIn(("kernel exploits", ["SC-02"]), lim)

    def test_esc(self):
        self.assertEqual(B.esc("a|b\nc"), "a\\|b c")


class Page(unittest.TestCase):
    def test_render_and_check(self):
        with mock.patch.object(B.MS, "collect", fake_measured):
            page = B.render()
            self.assertIn("No scenario is deployment-assured; independent human review is open", page)
            self.assertLessEqual(page.count("\n"), 300)
            ms = B.manifests()
            for sid in ms:
                self.assertIn("| %s | " % sid, page)
            self.assertIn("x \\| y", page)
            self.assertIn("## How to verify", page)
            self.assertIn("## Honest limits", page)
            with tempfile.TemporaryDirectory() as d:
                out = Path(d) / "OVERVIEW.md"
                with mock.patch.object(B, "OUT", out):
                    self.assertEqual(B.main(["--check"]), 1)      # missing
                    self.assertEqual(B.main([]), 0)
                    self.assertEqual(B.main(["--check"]), 0)
                    out.write_text(out.read_text() + "edit\n")
                    self.assertEqual(B.main(["--check"]), 1)      # drift


if __name__ == "__main__":
    unittest.main()
