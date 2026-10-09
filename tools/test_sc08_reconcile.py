#!/usr/bin/env python3
"""Regression checks for SC-08's actual-output vs approved-input digest fidelity.

These are synthetic, unprivileged, independent unit tests of the reconciler.
They are not a reenactment of the frozen SC-08 runtime evidence.
"""
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "scenarios" / "SC-08" / "harness" / "reconcile.py"
SPEC = importlib.util.spec_from_file_location("sc08_reconcile", PATH)
R = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(R)

A = "a" * 64
B = "b" * 64
P = "c" * 64


def setup():
    allow = {"scripts": [A, B], "interpreters": [P]}
    records = [{
        "seq": 0, "decision": "executed", "script": "/staging/a.py",
        "script_digest": A, "program_digest": P, "rc": 0,
        "config": {"by_path": False, "no_script_check": False},
    }]
    sentinel = [{"name": "a", "self_sha256": A}]
    return allow, records, sentinel


class ReconciliationFidelityTests(unittest.TestCase):
    def test_exact_digest_pair_passes(self):
        self.assertTrue(R.reconcile(*setup())["ok"])

    def test_different_still_allowlisted_script_rejected(self):
        allow, records, sentinel = setup()
        sentinel[0]["self_sha256"] = B
        out = R.reconcile(allow, records, sentinel)
        self.assertFalse(out["ok"])
        self.assertFalse(out["consistent"])
        self.assertTrue(any(d["source"] == "reconciliation" for d in out["defects"]))

    def test_missing_script_digest_rejected_even_with_allowed_sentinel(self):
        allow, records, sentinel = setup()
        del records[0]["script_digest"]
        self.assertFalse(R.reconcile(allow, records, sentinel)["ok"])

    def test_missing_interpreter_digest_rejected(self):
        allow, records, sentinel = setup()
        del records[0]["program_digest"]
        self.assertFalse(R.reconcile(allow, records, sentinel)["ok"])

    def test_reordered_repeated_digests_match_by_multiset(self):
        allow, records, sentinel = setup()
        records.append(dict(records[0], seq=1, script_digest=B, script="/staging/b.py"))
        sentinel.append({"name": "b", "self_sha256": B})
        sentinel.reverse()
        self.assertTrue(R.reconcile(allow, records, sentinel)["ok"])

    def test_missing_observed_execution_rejected(self):
        allow, records, sentinel = setup()
        self.assertFalse(R.reconcile(allow, records, [])["ok"])

    def test_path_control_not_reclassified_as_hashed(self):
        allow, records, sentinel = setup()
        records[0]["config"]["by_path"] = True
        records[0].pop("script_digest")
        records[0].pop("program_digest")
        # This intentional weakened path is evaluated by the independent
        # sentinel/allowlist checks, not falsely attributed to fd-pinning.
        sentinel[0]["self_sha256"] = "f" * 64
        out = R.reconcile(allow, records, sentinel)
        self.assertFalse(out["ok"])
        self.assertEqual(len(out["defects"]), 1)


if __name__ == "__main__":
    unittest.main()
