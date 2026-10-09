"""Adversarial local tests for *journal-only* SC-10 effect gate."""
from pathlib import Path
import json
import tempfile
import unittest

from atomic_store import AtomicPolicyJournal, canonical, sha

class CheckedEffectTests(unittest.TestCase):
    def test_atomic_effect_and_tightening(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "journal"
            store = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(store.handle(1, {"op":"emit", "host":"a","payload":"before","request_id":"b"})["emitted"], False)
            self.assertTrue(store.handle(9,{"op":"write","policy":{"allow":["a"]}})["ok"])
            self.assertEqual(store.handle(1,{"op":"emit","host":"a","payload":"before","request_id":"b"})["replayed"], False)
            self.assertTrue(store.handle(9,{"op":"write","policy":{"allow":[]}})["ok"])
            n = len(store.events)
            result = store.handle(1,{"op":"emit","host":"a","payload":"after","request_id":"c"})
            self.assertEqual(result["decision"],"deny")
            self.assertEqual(len(store.events), n)
            self.assertEqual(len(store.effects), 1)
            self.assertEqual(store.effects[0]["version"], 0)
            store.close()
            store = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(len(store.effects),1)
            self.assertEqual(store.handle(1,{"op":"emit","host":"a","payload":"before","request_id":"b"})["replayed"],True)
            self.assertEqual(len(store.events), n)
            self.assertFalse(store.handle(1,{"op":"emit","host":"a","payload":"different","request_id":"b"})["ok"])
            store.close()

    def test_rejects_forged_effect_even_if_chain_recomputed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "journal"
            s=AtomicPolicyJournal(path,admin_pid=9)
            s.handle(9,{"op":"write","policy":{"allow":["a"]}})
            s.handle(1,{"op":"emit","host":"a","payload":"x","request_id":"x"})
            s.close()
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            rows[1]["host"] = "forbidden"
            rows[1]["prev"] = sha(rows[0])
            path.write_bytes(b"".join(canonical(row)+b"\n" for row in rows))
            with self.assertRaisesRegex(ValueError, "invalid, duplicated, or stale"):
                AtomicPolicyJournal(path, admin_pid=9)

    def test_duplicate_replay_never_appends_second_effect(self):
        with tempfile.TemporaryDirectory() as d:
            s = AtomicPolicyJournal(Path(d)/"j",admin_pid=9)
            s.handle(9,{"op":"write","policy":{"allow":["a"]}})
            req = {"op":"emit","host":"a","payload":"x","request_id":"id"}
            first=s.handle(1,req)
            for _ in range(20):
                rep=s.handle(1,req)
                self.assertEqual(rep["seq"],first["seq"])
                self.assertTrue(rep["replayed"])
            self.assertEqual(len(s.effects),1)
            self.assertEqual(len(s.events),2)
            s.close()

    def test_rejects_invalid_shape(self):
        with tempfile.TemporaryDirectory() as d:
            s=AtomicPolicyJournal(Path(d)/"j",admin_pid=9)
            s.handle(9,{"op":"write","policy":{"allow":["a"]}})
            for req in [
                {"op":"emit","host":"a","payload":0,"request_id":"a"},
                {"op":"emit","host":"a","payload":"x","request_id":""},
                {"op":"emit","host":"a","payload":"x"*513,"request_id":"a"},
                {"op":"emit","host":"a","payload":"x","request_id":False},
            ]:
                self.assertFalse(s.handle(1,req)["ok"])
            self.assertEqual(len(s.effects),0)
            s.close()

if __name__ == "__main__":
    unittest.main()
