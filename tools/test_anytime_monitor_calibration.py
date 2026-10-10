"""Anytime-valid union bound, adaptive selection and fail-closed semantics."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tools.anytime_monitor_calibration import analyze, anytime_upper


def manifest(histories=None):
    return {
        "histories": histories or ["history-a"],
        "alpha": 0.05,
        "minimum_per_class": 30,
        "monitor_sha256": "a" * 64,
        "policy_sha256": "b" * 64,
        "max_miss_upper": 0.3,
        "max_false_alarm_upper": 0.3
    }


def sample(n, history="history-a", fails=0):
    return ([{"id": f"attack-{history}-{i}", "history": history,
              "attack": True, "alarm": i >= fails} for i in range(n)] +
            [{"id": f"benign-{history}-{i}", "history": history,
              "attack": False, "alarm": i < fails} for i in range(n)])


class AnytimeTests(unittest.TestCase):
    def test_radius_valid_for_optional_stopping_and_many_histories(self):
        for n in (1, 2, 10, 100, 1000):
            a = anytime_upper([False] * n, 2, 0.05)
            b = anytime_upper([False] * n, 20, 0.05)
            self.assertGreaterEqual(b, a)
            self.assertGreaterEqual(a, 0)
            self.assertLessEqual(a, 1)
        self.assertEqual(anytime_upper([True] * 100, 2, 0.05), 1)
        self.assertIsNone(anytime_upper([], 2, 0.05))

    def test_positive_witness_and_false_positive_gate(self):
        success = analyze(sample(500), manifest())
        self.assertTrue(success["limits_met"])
        self.assertEqual(success["status"], "conditional_average_limits_met")
        bad = analyze(sample(500, fails=250), manifest())
        self.assertFalse(bad["limits_met"])
        self.assertEqual(bad["status"], "conditional_average_limits_not_met")
        self.assertGreater(bad["strata"]["history-a"]["benign_conditional_average_upper"], .3)

    def test_missing_stratum_and_sparse_adaptation_fail_shut(self):
        result = analyze(sample(500), manifest(["history-a", "history-b"]))
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertEqual(result["families_tested"], 4)
        self.assertIsNone(result["strata"]["history-b"]["attack_conditional_average_upper"])
        self.assertEqual(analyze(sample(8), manifest())["status"], "insufficient_samples")

    def test_duplicate_episode_wrong_types_undeclared_history(self):
        with self.assertRaises(ValueError):
            analyze(sample(1) + sample(1), manifest())
        with self.assertRaises(ValueError):
            analyze([{"id": "x", "history": "wrong", "attack": True,
                      "alarm": False}], manifest())
        with self.assertRaises(ValueError):
            analyze([{"id": "x", "history": "history-a", "attack": 1,
                      "alarm": False}], manifest())
        with self.assertRaises(ValueError):
            analyze(sample(1), {**manifest(), "alpha": 1.0})

    def test_cli_receipt_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "episodes.jsonl"
            policy = root / "manifest.json"
            out = root / "receipt.json"
            inp.write_text("".join(json.dumps(x) + "\n" for x in sample(500)))
            policy.write_text(json.dumps(manifest()))
            cmd = [sys.executable, "-m", "tools.anytime_monitor_calibration",
                   "--input", str(inp), "--manifest", str(policy),
                   "--output", str(out)]
            self.assertEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            receipt = json.loads(out.read_text())
            self.assertTrue(receipt["limits_met"])
            self.assertEqual(len(receipt["input_sha256"]), 64)
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            self.assertEqual(receipt, json.loads(out.read_text()))
            out.unlink()
            out.symlink_to(root / "nonexistent")
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            self.assertFalse((root / "nonexistent").exists())


if __name__ == "__main__":
    unittest.main()
