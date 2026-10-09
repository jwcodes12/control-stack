"""Expected counterexamples delimiting the SHA-chained journal's trust roots.

These tests *succeed when attacks are possible* on a journal an attacker can
rewrite. They are NOT production tests, and must not be described as hardening.
"""
import json
from pathlib import Path
import tempfile
import unittest
from atomic_store import AtomicPolicyJournal, canonical, sha


class JournalCustodyCounterexamples(unittest.TestCase):
    def test_valid_prefix_rollback_is_undetectable_without_external_anchor(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'journal'
            s = AtomicPolicyJournal(path, admin_pid=9)
            s.handle(9, {'op':'write','policy':{'allow':['good']}})
            prefix = path.read_bytes()
            s.handle(9, {'op':'write','policy':{'allow':[]}})
            self.assertEqual(s.handle(1, {'op':'decide','host':'good'})['decision'],'deny')
            s.close()
            path.write_bytes(prefix)  # attacker controls whole journal path
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(s.handle(1, {'op':'decide','host':'good'})['decision'],'allow')
            s.close()

    def test_fake_admin_write_with_recomputed_chain_is_accepted(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'journal'
            s = AtomicPolicyJournal(path, admin_pid=9)
            s.handle(9, {'op':'write','policy':{'allow':[]}})
            s.close()
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            entry = {'kind':'write', 'version':1, 'writer_pid':9,
                     'policy':{'allow':['forged']},
                     'digest':sha({'allow':['forged']}),
                     'seq':1, 'prev':sha(rows[0])}
            with path.open('ab') as out:
                out.write(canonical(entry) + b'\n')
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(s.handle(1,{'op':'decide','host':'forged'})['decision'],'allow')
            s.close()


if __name__ == '__main__':
    unittest.main()
