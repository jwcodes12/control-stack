#!/usr/bin/env python3
"""Mutation controls for the static scenario checker. Does not run experiments."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import check_scenario as checked


class ScenarioCheckerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.previous = checked.ROOT
        checked.ROOT = self.root
        self.folder = self.root / "scenarios" / "SC-99"
        (self.folder / "tests").mkdir(parents=True)
        (self.root / "src").mkdir()
        (self.root / "src" / "Model.lean").write_text("theorem candidate : True := by trivial\n")
        (self.root / "src" / "negative_test.py").write_text("# mutation fixture\n")
        (self.root / "src" / "receipt.json").write_text('{"frozen": true}\n')
        (self.folder / "claim.lean").write_text("import ControlStack.EgressGate\n#print axioms ControlStack.EgressGate.trace_safe\n")
        (self.folder / "correspondence.md").write_text("Conditional only\n")
        (self.folder / "result.md").write_text("Not deployment assured\n")
        (self.folder / "tests" / "README.md").write_text("Fixtures are fake.\n")
        (self.folder / "policy.json").write_text(json.dumps({
            "kind": "POLICY_REFERENCE_NOT_ENFORCEMENT", "scenario_id": "SC-99"}))
        keys = ("id", "title", "sources", "threat_origin", "attacker_controlled",
                "protected_assets", "harmful_transition_or_event", "runtime_boundary",
                "permitted_actions", "forbidden_actions", "complete_receiver_observations",
                "secret_side_information", "horizon_and_persistent_state",
                "honest_task_distribution", "theorem_name", "theorem_assumptions",
                "trusted_computing_base", "checkers", "implementation_hashes",
                "negative_tests", "usefulness_metrics", "environment_evidence",
                "unresolved", "status", "reviewer_decisions")
        spec = {k: "explicit placeholder in test only" for k in keys}
        spec.update({"id": "SC-99", "title": "Fixture scenario", "status": "CONDITIONAL"})
        (self.folder / "scenario.yaml").write_text(json.dumps(spec))
        source_hash = self.hash("src/Model.lean")
        receipt_hash = self.hash("src/receipt.json")
        self.manifest = {
            "schema_version": 1, "id": "SC-99", "title": "Fixture scenario",
            "claim_scope": "Artificial unit-test claim; no real assurance or enforcement",
            "declared_status": "CONDITIONAL",
            "axes": {axis: {"status": "UNRESOLVED", "note": "Missing trusted runtime",
                            "evidence_ids": []} for axis in checked.AXES},
            "premises": [{"id": "needs_refinement", "axis": "runtime_correspondence",
                          "status": "UNRESOLVED", "text": "Correspondence not proved"}],
            "proofs": [{"file": "src/Model.lean", "theorem": "Fake.Model.candidate",
                        "sha256": source_hash, "adversary_class": "UNKNOWN",
                        "status_recorded": "NOT_CHECKED"}],
            "evidence": [{"id": "fixture-receipt", "path": "src/receipt.json",
                          "sha256": receipt_hash, "kind": "TEST_FIXTURE"}],
            "negative_tests": ["src/negative_test.py"]}
        self.write_manifest()

    def tearDown(self):
        checked.ROOT = self.previous
        self.tmp.cleanup()

    def hash(self, path):
        return hashlib.sha256((self.root / path).read_bytes()).hexdigest()

    def write_manifest(self):
        (self.folder / "manifest.json").write_text(json.dumps(self.manifest))

    def test_valid_undeployed_bundle(self):
        got = checked.validate_case(self.folder)
        self.assertEqual(got["declared_status"], "CONDITIONAL")

    def test_digest_mutation_fails_closed(self):
        (self.root / "src" / "receipt.json").write_text('{"frozen": false}\n')
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)

    def test_absent_axis_fails_closed(self):
        del self.manifest["axes"]["environment_boundary"]
        self.write_manifest()
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)

    def test_false_supported_axis_fails_closed(self):
        self.manifest["axes"]["threat_coverage"]["status"] = "SUPPORTED"
        self.write_manifest()
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)

    def test_unpinned_evidence_fails_closed(self):
        self.manifest["evidence"][0]["sha256"] = "0" * 64
        self.write_manifest()
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)

    def test_unearned_assurance_status_fails_closed(self):
        self.manifest["declared_status"] = "DEPLOYMENT_ASSURED"
        self.write_manifest()
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)

    def test_path_escape_fails_closed(self):
        self.manifest["evidence"][0]["path"] = "../outside.txt"
        self.write_manifest()
        with self.assertRaises(checked.InvalidCase):
            checked.validate_case(self.folder)


if __name__ == "__main__":
    unittest.main()
