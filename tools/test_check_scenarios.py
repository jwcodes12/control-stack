#!/usr/bin/env python3
"""Static checker tests; do not invoke agents, Lean, or VMs."""
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tools.check_scenarios import Invalid, main, verify, SCOPE_AXES
from tools.build_registry import DECL


class CheckerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.bundle = self.root / "scenarios" / "SC-01"
        (self.bundle / "tests").mkdir(parents=True)
        for p in ("threat.md", "claim.lean", "policy.json", "correspondence.md",
                  "result.md", "tests/README.md"):
            (self.bundle / p).write_text("placeholder")
        proof = self.root / "sample.lean"
        proof.write_text("theorem foo : True := by trivial")
        self.m = {
            "schema_version": 1, "id": "SC-01", "title": "test",
            "bad_event": "event", "adversary": "model", "refutation": "trace",
            "scope": "fixture", "families": ["F1"], "status": "CONDITIONAL",
            "theorems": [{"path": "sample.lean", "name": "foo",
                          "sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
                          "recorded_status": "KERNEL_CHECK_RECORDED"}],
            "evidence": [], "assumptions": [{"id": "boundary", "text": "exclusive gate",
                "proof": "THEOREM_VERIFIED", "evidence": "NOT_RUN",
                "applicability": "UNRESOLVED", "usefulness": "NOT_RUN"}],
            "scope_axes": {name: {"status": "UNRESOLVED", "note": "Not independently verified"}
                           for name in SCOPE_AXES}
        }
        (self.root / "THEOREM-REGISTRY.json").write_text(
            json.dumps([{"key": "sample.lean::foo", "status": "SOURCE_ONLY"}]))
        (self.bundle / "claim.lean").write_text("#check foo\n")
        self.save()

    def tearDown(self):
        self.tmp.cleanup()

    def save(self):
        (self.bundle / "manifest.json").write_text(json.dumps(self.m))

    def test_conditional_does_not_promote(self):
        r = verify(self.root, "SC-01")
        self.assertEqual(r["proof"], "RECORDED_NOT_RECHECKED")
        self.assertEqual(r["applicability"], "BLOCKED")
        self.assertFalse(r["deployment_assured"])

    def test_missing_assumption_axis_fails(self):
        del self.m["assumptions"][0]["evidence"]
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_missing_usefulness_fails_closed(self):
        del self.m["assumptions"][0]["usefulness"]
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_missing_scope_axis_fails_closed(self):
        del self.m["scope_axes"]["independent_review"]
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_false_scope_promotion_fails_closed(self):
        self.m["scope_axes"]["environment_boundary"]["status"] = "SUPPORTED"
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_usefulness_failure_is_reported(self):
        self.m["assumptions"][0]["usefulness"] = "OBSERVED_FAILURE"
        self.m["scope_axes"]["usefulness"]["status"] = "REFUTED"
        self.save()
        report = verify(self.root, "SC-01")
        self.assertEqual(report["usefulness"], "FAILED_RECORDED")
        self.assertEqual(report["applicability"], "BLOCKED")

    def test_duplicate_json_key_rejected(self):
        text = (self.bundle / "manifest.json").read_text()
        (self.bundle / "manifest.json").write_text(text.replace(
            '"schema_version": 1', '"schema_version": 1, "schema_version": 1'))
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_self_declared_runtime_validation_rejected(self):
        self.m["assumptions"][0]["evidence"] = "RUNTIME_VALIDATED"
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_self_declared_usefulness_promotion_rejected(self):
        self.m["assumptions"][0]["usefulness"] = "MET_RECORDED"
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_mismatched_hash_fails(self):
        self.m["theorems"][0]["sha256"] = "0" * 64
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_traversal_fails(self):
        self.m["theorems"][0]["path"] = "../../oops.lean"
        self.save()
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_failed_receipt_cannot_promote(self):
        p = self.root / "failed.json"
        p.write_text('{"passed":false}')
        self.m["evidence"] = [{"path": "failed.json", "sha256":
            hashlib.sha256(p.read_bytes()).hexdigest(), "purpose": "negative trial",
            "outcome": "FAIL"}]
        self.save()
        r = verify(self.root, "SC-01")
        self.assertEqual(r["evidence"], "FAILURE_RECORDED")
        self.assertEqual(r["applicability"], "BLOCKED")

    def test_strict_fails_conditional(self):
        self.assertEqual(main(["SC-01", "--require-clear"], root=self.root), 2)

    def test_unregistered_theorem_fails_closed(self):
        (self.root / "THEOREM-REGISTRY.json").write_text("[]")
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_missing_claim_query_fails_closed(self):
        (self.bundle / "claim.lean").write_text("import Std\n")
        with self.assertRaises(Invalid):
            verify(self.root, "SC-01")

    def test_registry_covers_simp_and_qualified_declarations(self):
        source = ("@[simp] theorem System.run_nil : True := by trivial\n"
                  "noncomputable theorem bound : True := by trivial\n")
        self.assertEqual(DECL.findall(source), ["System.run_nil", "bound"])

    def test_draft_has_no_proof(self):
        self.m["theorems"] = []
        self.m["status"] = "DRAFT"
        self.save()
        self.assertEqual(verify(self.root, "SC-01")["proof"], "NO_THEOREM_LISTED")


if __name__ == "__main__":
    unittest.main()
