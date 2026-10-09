#!/usr/bin/env python3
"""Consistency check: the scenario premise table encoded in ControlStack/Core/TrustRoot.lean equals the normalisation
computed by tools/portfolio_ledger.py from the scenario manifests. Live Lean call; skipped if `lake` is missing or
TRUST_ROOT_SKIP_LEAN=1. Also prints SC-26's root ledger."""
import os
import shutil
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tools import portfolio_ledger as pl  # noqa: E402
from tools.cert_ledger import lean_ledger  # noqa: E402

IMPORT = ("ControlStack.Core.TrustRoot",)


@unittest.skipIf(shutil.which("lake") is None or os.environ.get("TRUST_ROOT_SKIP_LEAN") == "1",
                 "lake unavailable or live Lean test disabled")
class TrustRootConsistency(unittest.TestCase):
    def test_scenario_premises_match_portfolio(self):
        lean = lean_ledger("ControlStack.TrustRoot.scenarioPremiseLedger", imports=IMPORT)
        lean_pairs = {(e["name"].split(":", 1)[0], e["name"].split(":", 1)[1]) for e in lean}
        lean_kinds = {e["name"].split(":", 1)[1]: e["kind"] for e in lean}
        rows = pl.build()
        tool_pairs = {(s, r["id"]) for r in rows for s in r["scenarios"]}
        self.assertEqual(lean_pairs, tool_pairs)
        for r in rows:
            if r["scenarios"]:
                self.assertEqual(lean_kinds[r["id"]], r["kind"], r["id"])

    def test_sc26_root_ledger(self):
        lean = lean_ledger("ControlStack.TrustRoot.sc26RootLedger", imports=IMPORT)
        names = [e["name"] for e in lean]
        self.assertTrue(all(n.startswith("SC-26 rests on: ") for n in names))
        self.assertIn("SC-26 rests on: issuer_authenticity", names)


if __name__ == "__main__":
    unittest.main(verbosity=2)
