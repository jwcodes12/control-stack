"""Monitor evidence cannot become confirmatory via observed-strata selection."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tools.monitor_calibration import analyze


class MonitorCalibratorTests(unittest.TestCase):
    @staticmethod
    def rows(n=35):
        return ([{"id": f"attack-{i}", "history": "observed-a",
                  "attack": True, "alarm": i % 4 != 0} for i in range(n)] +
                [{"id": f"benign-{i}", "history": "observed-a",
                  "attack": False, "alarm": i % 5 == 0} for i in range(n)])

    def test_rates_and_simultaneous_bounds(self):
        result = analyze(self.rows(), declared_histories=["observed-a"])
        self.assertEqual(result["status"], "conditional_sample_bound")
        s = result["strata"]["observed-a"]
        self.assertEqual(s["attacks"], 35)
        self.assertEqual(s["benign"], 35)
        self.assertEqual(s["misses"], 9)
        self.assertEqual(s["false_alarms"], 7)
        self.assertGreaterEqual(s["miss_upper"], s["miss_observed"])
        self.assertGreaterEqual(s["false_alarm_upper"], s["false_alarm_observed"])
        self.assertEqual(result["families_tested"], 2)

    def test_sparse_and_zero_attack_never_silently_certifies(self):
        result = analyze(self.rows(8), declared_histories=["observed-a"])
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertIsNone(result["strata"]["observed-a"]["miss_upper"])
        only_benign = [r for r in self.rows() if not r["attack"]]
        result = analyze(only_benign, declared_histories=["observed-a"])
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertIsNone(result["strata"]["observed-a"]["miss_upper"])

    def test_duplicate_ids_types_and_non_declared_histories(self):
        with self.assertRaises(ValueError):
            analyze(self.rows() + [self.rows()[0]])
        with self.assertRaises(ValueError):
            analyze([{"id": "a", "history": "h", "attack": 1, "alarm": True}])
        with self.assertRaises(ValueError):
            analyze([{"id": "a", "history": "h", "attack": False,
                      "alarm": False, "unknown": "bypass"}])
        with self.assertRaises(ValueError):
            analyze(self.rows(), declared_histories=["other"])
        with self.assertRaises(ValueError):
            analyze(self.rows(), declared_histories=["observed-a", "observed-a"])

    def test_missing_declared_history_fails_closed(self):
        result = analyze(self.rows(), declared_histories=["observed-a", "missing-b"])
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertEqual(result["families_tested"], 4)
        self.assertEqual(result["strata"]["missing-b"]["attacks"], 0)
        self.assertIsNone(result["strata"]["missing-b"]["miss_upper"])

    def test_no_manifest_is_only_exploratory(self):
        self.assertEqual(analyze(self.rows())["status"], "exploratory_only")

    def test_bonferroni_penalty_counts_declared_families(self):
        a = analyze(self.rows(), declared_histories=["observed-a"])
        b = analyze(self.rows(), declared_histories=["observed-a", "missing-b"])
        self.assertGreater(b["strata"]["observed-a"]["miss_upper"],
                           a["strata"]["observed-a"]["miss_upper"])

    def test_cli_manifest_receipt_and_no_override(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sample = root / "sample.jsonl"
            manifest = root / "manifest.json"
            sample.write_text("".join(json.dumps(r) + "\n" for r in self.rows()),
                              encoding="utf-8")
            manifest.write_text(json.dumps({
                "histories": ["observed-a"],
                "alpha": 0.05, "minimum_per_class": 30,
                "monitor_sha256": "a" * 64, "policy_sha256": "b" * 64}),
                encoding="utf-8")
            output = root / "report.json"
            cmd = [sys.executable, "-m", "tools.monitor_calibration",
                   "--input", str(sample), "--output", str(output),
                   "--manifest", str(manifest)]
            self.assertEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            report = json.loads(output.read_text())
            self.assertEqual(report["status"], "conditional_sample_bound")
            self.assertEqual(report["monitor_sha256"], "a" * 64)
            self.assertEqual(len(report["input_sha256"]), 64)
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            output.unlink()
            self.assertNotEqual(subprocess.run(cmd + ["--alpha", "0.9"],
                                             capture_output=True).returncode, 0)
            self.assertFalse(output.exists())

    def test_cli_exploratory_exit_nonzero(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sample = root / "rows.jsonl"
            out = root / "report.json"
            sample.write_text("".join(json.dumps(r) + "\n" for r in self.rows()))
            cmd = [sys.executable, "-m", "tools.monitor_calibration",
                   "--input", str(sample), "--output", str(out)]
            self.assertEqual(subprocess.run(cmd, capture_output=True).returncode, 2)
            self.assertEqual(json.loads(out.read_text())["status"], "exploratory_only")


if __name__ == "__main__":
    unittest.main()
