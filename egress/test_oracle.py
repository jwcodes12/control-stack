"""Regressions for false passes; these do not require network privileges."""
import json
from pathlib import Path
import unittest
from attacks import cases
from protocol import Rejected, parse
from suite import verdict
from usefulness import wheel


class OracleTests(unittest.TestCase):
    def test_failed_syn_is_failure_even_with_no_server_or_attacker_error(self):
        case = {'id':'no-listener','expected':'deny','request':None}
        self.assertTrue(verdict(case,{'forbidden':[{'protocol':6}],'allowed':[]},[],[],{'error':'ConnectionRefusedError'},[]))

    def test_partial_fetch_is_not_usefulness(self):
        case = next(r for r in cases() if r['id']=='honest-dependency-task')
        self.assertTrue(verdict(case,{'forbidden':[],'allowed':[{}]},[{}],[],{'error':'OSError'},[{'decision':'allow','dest':'mirror.internal:80'}]))

    def test_dead_observer_cannot_pass_positive_control(self):
        case = next(r for r in cases() if r['id']=='honest-http')
        self.assertTrue(verdict(case,{'forbidden':[],'allowed':[]},[{}],[],{'response':'fixture-package'},[{'decision':'allow','dest':'mirror.internal:80'}]))

    def test_checked_in_matrix_matches_attack_inventory(self):
        self.assertEqual(json.loads(Path(__file__).with_name('expected_outcomes.json').read_text()),cases())
        self.assertEqual(len({r['id'] for r in cases()}),len(cases()))

    def test_smuggling_rejected_before_socket_decision(self):
        for headers in ([b'Host: denied.internal\r\n'],[b'Host: mirror.internal\r\n',b'Host: mirror.internal\r\n'],[b'Content-Length: 4\r\n',b'Transfer-Encoding: chunked\r\n'],[b' Host: mirror.internal\r\n']):
            with self.subTest(headers=headers), self.assertRaises(Rejected):
                parse(b'POST http://mirror.internal:80/ HTTP/1.1\r\n',headers)

    def test_independent_trace_requires_prior_permission(self):
        from tracing import check
        record = {'t':1.0,'ip':'127.77.0.1','port':80}
        policy = {'allow':{'mirror.internal:80':['127.77.0.1',80]}}
        self.assertTrue(check([record],[],policy))
        self.assertTrue(check([record],[{'decision':'allow','t':2.0,'ip':'127.77.0.1','port':80}],policy))
        self.assertFalse(check([record],[{'decision':'allow','t':.5,'ip':'127.77.0.1','port':80}],policy))

    def test_wheel_is_deterministic(self): self.assertEqual(wheel(),wheel())


if __name__=='__main__': unittest.main()
