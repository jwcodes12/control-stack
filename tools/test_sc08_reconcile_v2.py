"""Regression tests for SC-08's supplementary digest/receipt reconciliation.

No runner, privileged operation, or evidence mutation. Pure synthetic receipts.
"""
import importlib.util
from pathlib import Path
import unittest

SRC = Path(__file__).resolve().parents[1] / "scenarios/SC-08/harness/reconcile_v2.py"
spec = importlib.util.spec_from_file_location("sc08_reconcile_v2", SRC)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

PD = "a" * 64
S1 = "b" * 64
S2 = "c" * 64
ALLOW = {"interpreters": [PD], "scripts": [S1, S2]}


def row(n, digest=S1):
    return {"seq": n, "decision": "executed", "program_digest": PD,
            "script_digest": digest, "script": "/untrusted/original.py",
            "executed_path": "/launcher/pin/" + digest + ".py", "rc": 0}


def receipt(digest=S1):
    return {"name": "benign", "self_sha256": digest}


class ReconcileTests(unittest.TestCase):
    def test_good(self):
        self.assertTrue(module.reconcile_v2(ALLOW, [row(0), row(1, S2)], [receipt(S2), receipt()])["ok"])

    def test_missing_program_digest_is_not_allowed(self):
        r = row(0)
        r.pop("program_digest")
        self.assertFalse(module.reconcile_v2(ALLOW, [r], [receipt()])["ok"])

    def test_missing_script_digest_is_not_allowed(self):
        r = row(0)
        r.pop("script_digest")
        self.assertFalse(module.reconcile_v2(ALLOW, [r], [receipt()])["ok"])

    def test_allowlisted_but_wrong_sentinel_digest_is_detected(self):
        self.assertFalse(module.reconcile_v2(ALLOW, [row(0)], [receipt(S2)])["ok"])

    def test_same_total_count_does_not_hide_misassigned_receipts(self):
        self.assertFalse(module.reconcile_v2(ALLOW, [row(0), row(1)], [receipt(), receipt(S2)])["ok"])

    def test_duplicate_sequence_fails(self):
        self.assertFalse(module.reconcile_v2(ALLOW, [row(0), row(0)], [receipt(), receipt()])["ok"])

    def test_unpinned_execution_fails(self):
        r = row(0)
        r["executed_path"] = "/tmp/untrusted.py"
        self.assertFalse(module.reconcile_v2(ALLOW, [r], [receipt()])["ok"])

    def test_nonzero_exit_fails(self):
        r = row(0)
        r["rc"] = 127
        self.assertFalse(module.reconcile_v2(ALLOW, [r], [])["ok"])

    def test_bad_sentinel_digest_fails(self):
        self.assertFalse(module.reconcile_v2(ALLOW, [row(0)], [{"self_sha256": "bad"}])["ok"])


if __name__ == "__main__":
    unittest.main()
