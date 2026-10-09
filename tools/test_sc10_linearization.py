"""Synthetic negative controls for SC-10 policy read-to-effect gap."""
import unittest
from tools.sc10_linearization import audit, digest


def ver(i, t, allow):
    policy = {"allow": allow}
    return {"version": i, "t_commit": t, "writer": "admin",
            "policy": policy, "digest": digest(policy)}


def dec(v, answer, effect):
    return {"version": v["version"], "digest": v["digest"],
            "length": v["version"] + 1, "host": "ok",
            "decision": "allow" if "ok" in v["policy"]["allow"] else "deny",
            "t_answer": answer, "t_decide": effect,
            "config": {"cache_ttl": None, "alt_file": False}}


class ReadEffectTests(unittest.TestCase):
    def setUp(self):
        self.first = ver(0, 10, ["ok"])
        self.second = ver(1, 21, [])

    def test_honest_trace(self):
        r = audit([self.first, self.second], [dec(self.first, 15, 16), dec(self.second, 22, 23)])
        self.assertTrue(r["ok"], r)

    def test_administrative_update_between_read_and_decision(self):
        r = audit([self.first, self.second], [dec(self.first, 20, 22)])
        self.assertEqual(r["read_mismatches"], 0)
        self.assertEqual(r["effect_mismatches"], 1)
        self.assertIn("not_latest_at_effect", [d["kind"] for d in r["defects"]])

    def test_stale_read_and_digest(self):
        d = dec(self.first, 22, 23)
        d["digest"] = "0" * 64
        r = audit([self.first, self.second], [d])
        self.assertEqual(r["read_mismatches"], 1)
        self.assertIn("reply_policy_mismatch", [p["kind"] for p in r["defects"]])

    def test_alternate_evaluator_rejected(self):
        d = dec(self.first, 15, 16)
        d["config"]["alt_file"] = True
        self.assertIn("not_deployed_configuration",
                      [p["kind"] for p in audit([self.first], [d])["defects"]])

    def test_bad_clock_or_commit_order(self):
        r = audit([self.first, ver(1, 9, [])], [])
        self.assertIn("invalid_commit_order", [p["kind"] for p in r["defects"]])
        r = audit([self.first], [dec(self.first, 16, 15)])
        self.assertIn("invalid_timestamps", [p["kind"] for p in r["defects"]])


if __name__ == "__main__":
    unittest.main()
