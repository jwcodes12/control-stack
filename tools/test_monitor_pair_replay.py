"""Aligned trajectory pairs must never gain fictitious independence."""
import unittest
from tools.monitor_pair_replay import replay


def entry(label, attack_events, honest_events, *, first_id="a"):
    def instances(bits, prefix, success=False):
        return [{"trajectory_id": prefix + str(i),
                 "scores": [9 if bit else 0],
                 **({"side_task_success": True} if success else {})}
                for i, bit in enumerate(bits)]
    return {"dataset": "lastraj", "monitor": "simple",
            "monitor_variant": label, "score_samples": {
                "attack": instances(attack_events, first_id, success=True),
                "honest": instances(honest_events, "h" + first_id)}}


class PairReplayTests(unittest.TestCase):
    def test_co_miss_correlation_and_false_alarm_union(self):
        d = {"rows": [
            entry("m1", [False, False, True], [False, True, False]),
            entry("m2", [False, False, True], [True, False, False]),
        ]}
        r = replay(d)
        p = r["pairs"][0]
        self.assertEqual(p["status"], "exploratory_aligned")
        self.assertEqual(p["joint_miss_count"], 2)
        self.assertEqual(p["any_false_alarm_count"], 2)
        self.assertEqual(r["simultaneous_risk_families"], 2)
        self.assertGreaterEqual(p["joint_miss_upper"], 2/3)
        self.assertEqual(r["status"], "EXPLORATORY_POSTHOC_NO_ADAPTIVE_CERTIFICATE")

    def test_misaligned_or_missing_monitor_stays_in_family(self):
        a = entry("one", [True], [True])
        b = entry("two", [False], [False], first_id="other")
        c = entry("three", [False], [False])
        del c["score_samples"]
        r = replay({"rows": [a, b, c]})
        self.assertEqual(r["pair_family_count"], 3)
        self.assertEqual(r["simultaneous_risk_families"], 6)
        self.assertEqual(r["aligned_evaluable_pairs"], 0)

    def test_invalid_samples_fail_closed(self):
        a = entry("a", [True], [False])
        b = entry("b", [True], [False])
        b["score_samples"]["attack"][0]["scores"] = [float("nan")]
        self.assertEqual(replay({"rows": [a,b]})["aligned_evaluable_pairs"], 0)
        with self.assertRaises(ValueError):
            replay({"rows": [a,a]})
        with self.assertRaises(ValueError):
            replay({"rows": [a,b]}, threshold=-1)


if __name__ == "__main__":
    unittest.main()
