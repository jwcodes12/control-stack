#!/usr/bin/env python3
"""Tests for tools/portfolio_ledger.py: fixture repos (fail-closed normalisation, ranking, drift check) plus checks on the
real repository and one live Lean comparison of `ControlStack.Cert.portfolioPremises` with the tool's top five
(skipped if `lake` is missing or PORTFOLIO_LEDGER_SKIP_LEAN=1)."""
import contextlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tools import portfolio_ledger as pl  # noqa: E402

FIX_PREMISES = {
    "credential_separation": dict(kind="environment", title="t", members=["*:credential_separation"],
                                  stack=["kms.credential_separation"]),
    "exclusive_effect_path": dict(kind="environment", title="t",
                                  members=["SC-01:single_route", "SC-02:exclusive_executor"], stack=[]),
    "honest_usefulness": dict(kind="measurement", title="t", members=["*:honest_usefulness"], stack=[]),
}


def assumption(aid, evidence="NOT_RUN", proof="NOT_PROVED"):
    return {"id": aid, "text": aid, "proof": proof, "evidence": evidence, "applicability": "UNRESOLVED",
            "usefulness": "NOT_APPLICABLE"}


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "stack").mkdir()
        (self.root / "stack/components.json").write_text(json.dumps({"components": [
            {"id": "kms", "practical": {"commodity": "SoftHSM on one box. More text."},
             "premises": [{"id": "credential_separation", "text": "no agent signs", "evidence": []}]}]}))
        self.write("SC-01", [assumption("credential_separation", "TESTED_NOT_PROVED"), assumption("single_route")],
                   evidence=[{"path": "scenarios/SC-01/evidence/run-3/v.json", "outcome": "PASS"}])
        self.write("SC-02", [assumption("credential_separation"), assumption("exclusive_executor"),
                             assumption("honest_usefulness", "OBSERVED_FAILURE")])
        self.write("SC-03", [assumption("credential_separation")])

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, sid, assumptions, evidence=()):
        d = self.root / "scenarios" / sid
        d.mkdir(parents=True, exist_ok=True)
        (d / "manifest.json").write_text(json.dumps({"id": sid, "assumptions": assumptions,
                                                     "evidence": list(evidence)}))

    def build(self, premises=FIX_PREMISES):
        return {r["id"]: r for r in pl.build(self.root, premises)}

    def test_normalisation_and_leverage(self):
        rows = self.build()
        cs = rows["credential_separation"]
        self.assertEqual(cs["scenarios"], ["SC-01", "SC-02", "SC-03"])
        self.assertTrue(cs["tested"])
        self.assertEqual(cs["leverage"], 3)  # tested: × 1
        self.assertEqual(cs["runs"], ["SC-01 run-3"])
        self.assertEqual(cs["practical"][0]["commodity_test"], "SoftHSM on one box. More text.")
        ex = rows["exclusive_effect_path"]
        self.assertEqual(ex["leverage"], 4)  # 2 scenarios × 2 (untested)
        hu = rows["honest_usefulness"]
        self.assertEqual(hu["failures"], ["SC-02"])
        self.assertEqual(hu["best_evidence"], "OBSERVED_FAILURE")
        ranked = [r["id"] for r in pl.build(self.root, FIX_PREMISES)]
        self.assertEqual(ranked[0], "exclusive_effect_path")

    def test_unmapped_assumption_fails(self):
        self.write("SC-04", [assumption("brand_new_premise")])
        with self.assertRaises(pl.LedgerError) as e:
            self.build()
        self.assertIn("SC-04:brand_new_premise", str(e.exception))

    def test_double_mapping_fails(self):
        bad = dict(FIX_PREMISES, dup=dict(kind="measurement", title="t", members=["SC-01:single_route"], stack=[]))
        with self.assertRaises(pl.LedgerError):
            self.build(bad)

    def test_missing_member_and_stack_ref_fail(self):
        bad = dict(FIX_PREMISES, ghost=dict(kind="measurement", title="t", members=["SC-01:nope"], stack=[]))
        with self.assertRaises(pl.LedgerError):
            self.build(bad)
        bad = dict(FIX_PREMISES)
        bad["honest_usefulness"] = dict(FIX_PREMISES["honest_usefulness"], stack=["kms.nope"])
        with self.assertRaises(pl.LedgerError):
            self.build(bad)

    def test_bad_kind_fails(self):
        bad = dict(FIX_PREMISES)
        bad["honest_usefulness"] = dict(FIX_PREMISES["honest_usefulness"], kind="vibes")
        with self.assertRaises(pl.LedgerError):
            self.build(bad)

    def test_check_detects_drift(self):
        out = self.root / "ASSURANCE-LEDGER.md"
        old = pl.PREMISES
        pl.PREMISES = FIX_PREMISES
        try:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(pl.main(["--no-lean"], root=self.root, out=out), 0)
                self.assertEqual(pl.main(["--no-lean", "--check"], root=self.root, out=out), 0)
                out.write_text(out.read_text().replace("SC-03", "SC-99", 1))
                self.assertEqual(pl.main(["--no-lean", "--check"], root=self.root, out=out), 1)
        finally:
            pl.PREMISES = old


class RepoTests(unittest.TestCase):
    def test_every_real_assumption_normalised(self):
        rows = pl.build()
        self.assertGreater(len(rows), 10)
        self.assertEqual(rows[0]["id"], "credential_separation")

    def test_committed_ledger_matches(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(pl.main(["--check", "--no-lean"]), 0)


@unittest.skipIf(shutil.which("lake") is None or os.environ.get("PORTFOLIO_LEDGER_SKIP_LEAN") == "1",
                 "lake unavailable or live Lean test disabled")
class LeanAgreement(unittest.TestCase):
    def test_lean_portfolio_premises_match_top_five(self):
        from tools.cert_ledger import lean_ledger
        lean = lean_ledger("ControlStack.Cert.portfolioPremises")
        top = pl.build()[:5]
        self.assertEqual([(e["name"], e["kind"]) for e in lean], [(r["id"], r["kind"]) for r in top])


if __name__ == "__main__":
    unittest.main(verbosity=2)
