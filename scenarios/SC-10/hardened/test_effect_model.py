"""Bounded independent reference model for SC-10 journal effect transition semantics.

This checks an in-process *model and reference implementation*, NOT a live
firewall, OS principal separation, parser completeness, or Lean refinement.
"""
import random
from pathlib import Path
import tempfile
import unittest
from atomic_store import AtomicPolicyJournal


class Oracle:
    def __init__(self):
        self.versions = []
        self.effects = {}
        self.seq = 0
        self.entries = []

    def apply(self, pid, req):
        op = req['op']
        if op == 'write':
            if pid != 9:
                return {'ok': False, 'error': 'admin pid required'}
            pol = {'allow': list(req['policy']['allow'])}
            v = len(self.versions)
            self.versions.append(pol)
            self.entries.append(('write', v))
            n = self.seq
            self.seq += 1
            return {'ok': True, 'version': v, 'seq': n}
        if op == 'decide':
            if not self.versions:
                return {'ok': False, 'error': 'no policy'}
            v = len(self.versions) - 1
            decision = 'allow' if req['host'] in self.versions[-1]['allow'] else 'deny'
            n = self.seq
            self.seq += 1
            self.entries.append(('decide', v, decision))
            return {'ok': True, 'decision': decision, 'version': v, 'seq': n}
        if op == 'emit':
            rid = req['request_id']
            old = self.effects.get(rid)
            if old is not None:
                if (old['host'], old['payload']) != (req['host'], req['payload']):
                    return {'ok': False, 'error': 'idempotency key reused for different effect'}
                return {'ok': True, 'emitted': True, 'replayed': True, 'seq': old['seq'], 'version': old['version']}
            if not self.versions:
                return {'ok': False, 'emitted': False, 'error': 'no policy'}
            v = len(self.versions) - 1
            if req['host'] not in self.versions[-1]['allow']:
                return {'ok': False, 'emitted': False, 'decision': 'deny'}
            n = self.seq
            self.seq += 1
            rec = {'host': req['host'], 'payload': req['payload'], 'version': v, 'seq': n}
            self.effects[rid] = rec
            self.entries.append(('effect', v, req['host'], req['payload'], rid))
            return {'ok': True, 'emitted': True, 'replayed': False, 'seq': n, 'version': v}
        raise AssertionError('not generated')


class ModelDifferentialTests(unittest.TestCase):
    def test_bounded_deterministic_traces_with_restart(self):
        for seed in range(20):
            rng = random.Random(seed)
            model = Oracle()
            with tempfile.TemporaryDirectory(prefix='sc10-model-') as d:
                path = Path(d) / 'journal'
                actual = AtomicPolicyJournal(path, admin_pid=9)
                try:
                    for step in range(48):
                        kind = rng.choice(('write', 'decide', 'emit', 'emit', 'emit'))
                        pid = rng.choice((9, 1))
                        if kind == 'write':
                            req = {'op':'write', 'policy':{'allow': rng.choice(([],['a'],['b'],['a','b']))}}
                        elif kind == 'decide':
                            req = {'op':'decide', 'host': rng.choice(('a','b','x'))}
                        else:
                            req = {'op':'emit', 'host': rng.choice(('a','b','x')),
                                   'payload': rng.choice(('one','two')),
                                   'request_id': str(rng.randrange(5))}
                        expected = model.apply(pid,req)
                        observed = actual.handle(pid,req)
                        for k, value in expected.items():
                            self.assertEqual(observed.get(k), value,
                                f'seed={seed} step={step} request={req} key={k}')
                        self.assertEqual(len(actual.events), model.seq)
                        self.assertEqual(len(actual.effects), len(model.effects))
                        # Every accepted effect must be justified by the very
                        # policy version current at its journal position.
                        idx = 0
                        current = None
                        actual_effect_ids = set()
                        for e in actual.events:
                            if e['kind'] == 'write':
                                current = e['policy']['allow']
                                idx += 1
                            elif e['kind'] == 'effect':
                                self.assertIn(e['host'], current)
                                self.assertEqual(e['version'], idx - 1)
                                self.assertNotIn(e['request_id'], actual_effect_ids)
                                actual_effect_ids.add(e['request_id'])
                        if step in (11, 23, 35):
                            actual.close()
                            actual = AtomicPolicyJournal(path, admin_pid=9)
                            self.assertEqual(len(actual.effects), len(model.effects))
                finally:
                    actual.close()


if __name__ == '__main__':
    unittest.main()
