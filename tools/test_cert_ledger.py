#!/usr/bin/env python3
"""Tests for tools/cert_ledger.py: canned-JSON unit tests plus one live Lean call (skipped if `lake` is missing or
CERT_LEDGER_SKIP_LEAN=1)."""
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
from tools.cert_ledger import (KINDS, LedgerError, ROOT, check_manifest, grouped, lean_ledger, main, premise_id,
                               validate)

CANNED = [
    {"name": "SC26.legal: no untrusted operation carries the gate credential", "kind": "environment"},
    {"name": "SC26.sound_config: payload, distinct, cap, receiver dedup and auth checks enabled",
     "kind": "correspondence"},
    {"name": "F6.recall: per-history recall", "kind": "measurement"},
    {"name": "F6.recall: per-history recall", "kind": "measurement"},
    {"name": "F5.global_cap: payment damage ≤ SC-26 cap", "kind": "proof_obligation",
     "theorem": "ControlStack.SC26.sc26_safe"},
]


class LedgerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.manifest = self.dir / "manifest.json"
        self.registry = self.dir / "registry.json"
        self.write_manifest(["credential_separation", "model_runtime_correspondence", "receiver_idempotency"])
        self.registry.write_text(json.dumps([{"key": "ControlStack/Scenarios/SC26Transaction.lean::sc26_safe"}]))

    def tearDown(self):
        self.tmp.cleanup()

    def write_manifest(self, ids, sid="SC-26"):
        self.manifest.write_text(json.dumps({"id": sid, "assumptions": [{"id": i} for i in ids]}))

    def check(self, entries=CANNED):
        return check_manifest(entries, self.manifest, self.registry)

    def test_premise_id(self):
        self.assertEqual(premise_id("SC26.legal: text: more"), "SC26.legal")

    def test_grouping_dedups_and_orders(self):
        g = grouped(CANNED)
        self.assertEqual(list(g), list(KINDS))
        self.assertEqual(len(g["measurement"]), 1)
        self.assertTrue(g["proof_obligation"][0].endswith("[discharged by ControlStack.SC26.sc26_safe]"))
        self.assertEqual(g["organisational"], [])

    def test_manifest_pass(self):
        self.assertEqual(self.check(), [])

    def test_missing_assumption_fails(self):
        self.write_manifest(["credential_separation", "model_runtime_correspondence"])
        f = self.check()
        self.assertTrue(any("receiver_idempotency" in x for x in f), f)

    def test_unmapped_scenario_premise_fails(self):
        f = self.check(CANNED + [{"name": "SC26.new_thing: unmapped", "kind": "organisational"}])
        self.assertTrue(any("no manifest mapping" in x for x in f), f)

    def test_proof_obligation_needs_registry_theorem(self):
        self.registry.write_text(json.dumps([{"key": "X.lean::other"}]))
        f = self.check()
        self.assertTrue(any("sc26_safe" in x for x in f), f)

    def test_ambiguous_registry_theorem_fails(self):
        self.registry.write_text(json.dumps([{"key": "A.lean::sc26_safe"}, {"key": "B.lean::sc26_safe"}]))
        self.assertTrue(any("found 2 times" in x for x in self.check()))

    def test_unrelated_manifest_fails_closed(self):
        self.write_manifest(["credential_separation"], sid="SC-03")
        f = self.check()
        self.assertTrue(any("nothing to check" in x for x in f), f)

    def test_malformed_manifest_fails(self):
        self.manifest.write_text("{not json")
        self.assertTrue(self.check()[0].startswith("manifest unreadable"))

    def test_validate_rejects_bad_kind_and_missing_theorem(self):
        with self.assertRaises(LedgerError):
            validate([{"name": "x", "kind": "vibes"}])
        with self.assertRaises(LedgerError):
            validate([{"name": "x", "kind": "proof_obligation"}])
        with self.assertRaises(LedgerError):
            validate([])

    def test_cli_with_canned_json(self):
        canned = self.dir / "ledger.json"
        canned.write_text(json.dumps(CANNED))
        args = ["--json-file", str(canned), "--check-manifest", str(self.manifest), "--registry", str(self.registry),
                "--json"]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(args), 0)
            self.write_manifest([])
            self.assertEqual(main(args), 1)

    def test_rejects_non_identifier_ledger(self):
        with self.assertRaises(LedgerError):
            lean_ledger("x) ; #eval evil (")


@unittest.skipIf(shutil.which("lake") is None or os.environ.get("CERT_LEDGER_SKIP_LEAN") == "1",
                 "lake unavailable or live Lean test disabled")
class LiveLeanTest(unittest.TestCase):
    def test_live_stack_ledger_against_sc26_manifest(self):
        entries = lean_ledger()
        names = {premise_id(e["name"]) for e in entries}
        self.assertIn("SC26.legal", names)
        self.assertIn("F5.global_cap", names)
        po = [e for e in entries if e["kind"] == "proof_obligation"]
        self.assertEqual([e["theorem"] for e in po], ["ControlStack.SC26.sc26_safe"])
        self.assertEqual(check_manifest(entries, ROOT / "scenarios/SC-26/manifest.json"), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
