#!/usr/bin/env python3
"""Synthetic negative controls for SC-10 temporal reconciliation."""
import unittest
from sc10_temporal_audit import _digest, check_trace


def good():
    p0, p1 = {'allow': ['a.example']}, {'allow': []}
    rows = [
        {'version': 0, 'policy': p0, 'digest': _digest(p0), 'writer': 'admin'},
        {'commit': 0, 't': 100},
        {'version': 1, 'policy': p1, 'digest': _digest(p1), 'writer': 'admin'},
        {'commit': 1, 't': 250},
    ]
    decisions = [{'host': 'a.example', 'decision': 'allow', 'version': 0,
                  'length': 1, 'digest': _digest(p0), 't_answer': 150, 't_decide': 200}]
    return rows, decisions


class TemporalAuditTests(unittest.TestCase):
    def test_uncontested(self):
        rows, ds = good()
        self.assertTrue(check_trace(rows, ds)['ok'])

    def test_read_use_race_is_ambiguous_not_proven_bad(self):
        rows, ds = good()
        rows[-1]['t'] = 175
        result = check_trace(rows, ds)
        self.assertTrue(result['read_snapshot_valid'])
        self.assertFalse(result['ok'])
        self.assertEqual(result['ambiguous'][0]['committed_during_read_use'], [1])

    def test_stale_at_read_is_invalid(self):
        rows, ds = good()
        ds[0]['t_answer'], ds[0]['t_decide'] = 260, 270
        self.assertFalse(check_trace(rows, ds)['read_snapshot_valid'])

    def test_forged_digest_and_decision(self):
        rows, ds = good()
        ds[0]['digest'] = 'x'
        ds[0]['decision'] = 'deny'
        self.assertFalse(check_trace(rows, ds)['read_snapshot_valid'])

    def test_undated_store_and_vacuity_fail(self):
        rows, ds = good()
        self.assertFalse(check_trace(rows[:-1], ds)['ok'])
        self.assertFalse(check_trace(rows, [])['ok'])

    def test_reversed_clock_fails(self):
        rows, ds = good()
        ds[0]['t_answer'] = 220
        ds[0]['t_decide'] = 210
        self.assertFalse(check_trace(rows, ds)['ok'])

    def test_wrong_writer_fails(self):
        rows, ds = good()
        rows[0]['writer'] = 'pid:1'
        self.assertFalse(check_trace(rows, ds)['read_snapshot_valid'])

    def test_duplicate_commit_fails(self):
        rows, ds = good()
        rows.append({'commit': 0, 't': 110})
        self.assertFalse(check_trace(rows, ds)['read_snapshot_valid'])


if __name__ == '__main__':
    unittest.main()
