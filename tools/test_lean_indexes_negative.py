"""Negative controls for the checked-in 187-claim environment index parser.

Model-written/model-reviewed. This tests fail-closed parsing, not Lean or fidelity.
"""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools import build_lean_traceability as trace


def inventory():
    rows = [
        {"ordinal": i, "lean": f"ControlStack.Example.claim{i}",
         "direct": ["ControlStack.Example.Helper"],
         "dependencies": ["ControlStack.Example.Helper"],
         "axioms": ["propext"], "axioms_standard": True}
        for i in range(1, 188)
    ]
    return {"claim_count": 187, "claims": rows}


class DependencyInventoryNegativeControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.dir = Path(self.temp.name)
        self.patcher = patch.object(trace, "PARTS", self.dir)
        self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def parse(self, obj):
        (self.dir / "DEPENDENCIES.json").write_text(json.dumps(obj))
        return trace.dependencies()

    def test_valid_complete_standard_inventory(self):
        self.assertEqual(len(self.parse(inventory())), 187)

    def test_missing_claim_fails_closed(self):
        doc = inventory()
        doc["claims"].pop()
        with self.assertRaises(ValueError):
            self.parse(doc)

    def test_duplicate_ordinal_fails_closed(self):
        doc = inventory()
        doc["claims"][1]["ordinal"] = 1
        with self.assertRaises(ValueError):
            self.parse(doc)

    def test_nonstandard_axiom_fails_closed(self):
        doc = inventory()
        doc["claims"][0]["axioms"] = ["ControlStack.unsafeAxiom"]
        doc["claims"][0]["axioms_standard"] = False
        with self.assertRaises(ValueError):
            self.parse(doc)

    def test_forged_axiom_verdict_fails_closed(self):
        doc = inventory()
        doc["claims"][0]["axioms"] = ["sorryAx"]
        with self.assertRaises(ValueError):
            self.parse(doc)

    def test_truncated_closure_fails_closed(self):
        doc = inventory()
        doc["claims"][0]["dependencies"] = []
        with self.assertRaises(ValueError):
            self.parse(doc)

    def test_duplicate_dependency_fails_closed(self):
        doc = inventory()
        doc["claims"][0]["direct"] = ["ControlStack.Example.Helper"] * 2
        with self.assertRaises(ValueError):
            self.parse(doc)


if __name__ == "__main__":
    unittest.main()
