"""Statistical monitor audit must never certify missing labels or sparse strata."""
import unittest

from tools.monitor_calibration import analyze


class MonitorCalibratorTests(unittest.TestCase):
    @staticmethod
    def rows(n=35):
        return ([{"id": f"attack-{i}", "history": "observed-a",
                  "attack": True, "alarm": i % 4 != 0} for i in range(n)] +
                [{"id": f"benign-{i}", "history": "observed-a",
                  "attack": False, "alarm": i % 5 == 0} for i in range(n)])

    def test_rates_and_simultaneous_bounds(self):
        result = analyze(self.rows())
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
        result = analyze(self.rows(8))
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertIsNone(result["strata"]["observed-a"]["miss_upper"])
        only_benign = [r for r in self.rows() if not r["attack"]]
        result = analyze(only_benign)
        self.assertEqual(result["status"], "insufficient_samples")
        self.assertIsNone(result["strata"]["observed-a"]["miss_upper"])

    def test_duplicate_ids_invalid_types_and_unobserved_history(self):
        with self.assertRaises(ValueError):
            analyze(self.rows() + [self.rows()[0]])
        with self.assertRaises(ValueError):
            analyze([{"id": "a", "history": "h", "attack": 1, "alarm": True}])
        with self.assertRaises(ValueError):
            analyze([{"id": "a", "history": "h", "attack": False,
                      "alarm": False, "unknown": "bypass"}])
        split = self.rows() + [{"id": "sparse-a", "history": "adaptive-new",
                               "attack": True, "alarm": False}]
        self.assertEqual(analyze(split)["status"], "insufficient_samples")

    def test_bonferroni_number_of_histories_tightens_bounds(self):
        rows = self.rows()
        a = analyze(rows)["strata"]["observed-a"]["miss_upper"]
        rows += [{"id": "b-" + r["id"], "history": "observed-b",
                  "attack": r["attack"], "alarm": r["alarm"]}
                 for r in self.rows()]
        self.assertGreater(analyze(rows)["strata"]["observed-a"]["miss_upper"], a)


if __name__ == "__main__":
    unittest.main()
