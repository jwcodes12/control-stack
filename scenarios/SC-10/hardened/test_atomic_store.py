"""Source-only tests for SC-10 atomic receipt store v2 (no external effects)."""
import json
from pathlib import Path
import tempfile
import unittest
from atomic_store import AtomicPolicyJournal, canonical


class AtomicStoreTests(unittest.TestCase):
    def test_write_decide_recovery_and_seq(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log.jsonl'
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertFalse(s.handle(1, {'op':'write', 'policy': {'allow':['a']}})['ok'])
            self.assertEqual(s.handle(9, {'op':'write', 'policy': {'allow':['a']}})['version'],0)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['decision'],'allow')
            self.assertEqual(s.handle(9, {'op':'write', 'policy': {'allow':[]}})['version'],1)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['decision'],'deny')
            s.close()
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(len(s.versions),2)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['version'],1)
            self.assertEqual([e['seq'] for e in s.events], list(range(len(s.events))))
            s.close()

    def test_fail_closed_truncation(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'log'
            path.write_bytes(b'{"seq":0,')
            with self.assertRaises(ValueError):
                AtomicPolicyJournal(path, admin_pid=9)

    def test_fail_closed_altered_past_entry(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'log'
            s=AtomicPolicyJournal(path, admin_pid=9)
            s.handle(9, {'op':'write','policy':{'allow':['a']}})
            s.close()
            raw=path.read_text().replace('"a"','"b"')
            path.write_text(raw)
            with self.assertRaises(ValueError):
                AtomicPolicyJournal(path, admin_pid=9)

    def test_unapproved_formats_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            s=AtomicPolicyJournal(Path(d)/'log', admin_pid=9)
            for p in [{'allow':['a','a']}, {'allow':['a'], 'eval':'true'}, {'allow':[123]}, {'allow':'a'}]:
                self.assertFalse(s.handle(9, {'op':'write', 'policy':p})['ok'])
            self.assertFalse(s.handle(1,{'op':'decide','host':'a'})['ok'])
            s.close()


if __name__ == '__main__':
    unittest.main()
