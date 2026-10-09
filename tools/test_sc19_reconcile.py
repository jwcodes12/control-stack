#!/usr/bin/env python3
"""SC-19 independent gate/DB bidirectional reconciliation mutation tests.

Synthetic fixtures; no claim about frozen evidence or a production database.
"""
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "scenarios" / "SC-19" / "harness" / "reconcile.py"
SPEC = importlib.util.spec_from_file_location("sc19_reconcile", PATH)
R = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(R)


def valid_fixture():
    op = {"id": "one", "target": "prod", "kind": "delete_all", "author": "agent:5"}
    gate = dict(op, digest=R.op_digest(op), snap_id="snap", t=200,
                ver_destroyed=0, actual=2)
    hist = [{"kind": "destroy:one", "target": "prod", "ver_after": 1,
             "rows_changed": 2, "rows_hash": "rows-a"}]
    verifs = [{"verified": True, "snap_id": "snap", "t": 100,
               "targets": {"prod": {"ver": 0, "hash": "rows-a"}}}]
    approvals = [{"id": "one", "digest": gate["digest"], "op": op,
                  "author": "agent:5", "approver_pid": 9, "t": 150}]
    return [gate], verifs, approvals, hist, 4


class SC19ReconciliationTests(unittest.TestCase):
    def test_honest_gate_database_verifier_and_approver_agree(self):
        self.assertTrue(R.reconcile(*valid_fixture())["ok"])

    def test_unlogged_destructive_database_effect_rejected(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        hist.append(dict(hist[0], kind="destroy:out-of-band"))
        out = R.reconcile(gates, verifs, approvals, hist, cap)
        self.assertFalse(out["ok"])
        self.assertTrue(any(d["id"] == "out-of-band" for d in out["defects"]))

    def test_database_target_substitution_rejected(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        hist[0]["target"] = "another-production-target"
        self.assertFalse(R.reconcile(gates, verifs, approvals, hist, cap)["ok"])

    def test_forged_gate_digest_rejected(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        gates[0]["digest"] = "f" * 64
        approvals[0]["digest"] = gates[0]["digest"]
        self.assertFalse(R.reconcile(gates, verifs, approvals, hist, cap)["ok"])

    def test_affected_rows_must_match_database(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        gates[0]["actual"] += 1
        self.assertFalse(R.reconcile(gates, verifs, approvals, hist, cap)["ok"])

    def test_destroyed_version_must_match_database(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        gates[0]["ver_destroyed"] += 1
        self.assertFalse(R.reconcile(gates, verifs, approvals, hist, cap)["ok"])

    def test_duplicate_gate_record_rejected(self):
        gates, verifs, approvals, hist, cap = valid_fixture()
        gates.append(dict(gates[0]))
        self.assertFalse(R.reconcile(gates, verifs, approvals, hist, cap)["ok"])


if __name__ == "__main__":
    unittest.main()
