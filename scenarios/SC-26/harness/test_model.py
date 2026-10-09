#!/usr/bin/env python3
"""Unit tests for model.py: the Lean necessity witnesses (one check off -> concrete bad trace), the honest nuance
about the gate-side nonce, and random-trace preservation of `Inv` under the full checks with legal operations."""
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model as M  # noqa: E402

AG, AG2, AP, AD, GATE = 1, 2, 3, 4, 9
R = M.Roles((AG, AG2), (AP,), (AD,), GATE)
T1 = (7, 5, 11)
T2 = (8, 5, 11)


def off(**kw):
    return M.FULL._replace(**kw)


class Witnesses(unittest.TestCase):
    def test_full_happy_path(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.execute(AG, 0), M.deliver(0), M.arrive(0)]
        s = M.run(R, 10, M.FULL, M.INIT, ops)
        self.assertEqual(s.bank, ((0, M.Tx(*T1)),))
        self.assertTrue(M.good(R, 10, s))
        self.assertEqual(M.inv(R, 10, s), [])

    def test_payload_unchecked_breaks(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T2), M.execute(AG, 0), M.deliver(0), M.arrive(0)]
        self.assertEqual(M.run(R, 10, M.FULL, M.INIT, ops).bank, ())
        s = M.run(R, 10, off(payload=False), M.INIT, ops)
        self.assertEqual(s.bank, ((0, M.Tx(*T1)),))
        self.assertFalse(M.good(R, 10, s))

    def test_no_dedup_retry_duplicates(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.execute(AG, 0), M.deliver(0), M.arrive(0), M.arrive(0)]
        self.assertTrue(M.good(R, 10, M.run(R, 10, M.FULL, M.INIT, ops)))
        s = M.run(R, 10, off(bankDedup=False), M.INIT, ops)
        self.assertEqual(len(s.bank), 2)
        self.assertFalse(M.good(R, 10, s))

    def test_no_cap_breaks(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.execute(AG, 0), M.deliver(0), M.arrive(0)]
        self.assertEqual(M.run(R, 4, M.FULL, M.INIT, ops).bank, ())
        s = M.run(R, 4, off(cap=False), M.INIT, ops)
        self.assertFalse(M.good(R, 4, s))

    def test_no_halt_check_breaks(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.halt(AD), M.execute(AG, 0), M.deliver(0), M.arrive(0)]
        self.assertEqual(M.run(R, 10, M.FULL, M.INIT, ops).bank, ())
        s = M.run(R, 10, off(haltCheck=False), M.INIT, ops)
        self.assertTrue(s.halted and len(s.bank) == 1)

    def test_inflight_after_halt(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.execute(AG, 0), M.deliver(0), M.halt(AD), M.arrive(0)]
        s = M.run(R, 10, M.FULL, M.INIT, ops)
        self.assertEqual(s.bank, ((0, M.Tx(*T1)),))
        self.assertTrue(s.halted and M.good(R, 10, s))

    def test_gate_credential_leak_breaks(self):
        o = M.bankCall(GATE, 0, T1)
        self.assertFalse(M.legal(R, o))
        s = M.run(R, 10, M.FULL, M.INIT, [o])
        self.assertEqual(len(s.bank), 1)
        self.assertFalse(M.good(R, 10, s))
        self.assertEqual(M.run(R, 10, M.FULL, M.INIT, [M.bankCall(AG, 0, T1)]).bank, ())

    def test_self_approval_without_distinct_check(self):
        R2 = M.Roles((AG,), (AG,), (AD,), GATE)  # overlapping roles
        ops = [M.request(AG, T1), M.approve(AG, 0, T1), M.execute(AG, 0), M.deliver(0), M.arrive(0)]
        self.assertEqual(M.run(R2, 10, M.FULL, M.INIT, ops).bank, ())
        s = M.run(R2, 10, off(distinct=False), M.INIT, ops)
        self.assertFalse(M.good(R2, 10, s))

    def test_nonce_protects_budget_only(self):
        ops = [M.request(AG, T1), M.approve(AP, 0, T1), M.execute(AG, 0), M.execute(AG, 0), M.deliver(0), M.arrive(0), M.arrive(0)]
        s = M.run(R, 10, off(nonce=False), M.INIT, ops)
        self.assertEqual(len(s.bank), 1)       # the idempotent bank still yields one effect
        self.assertEqual(s.spent, 10)          # but the budget is charged twice
        self.assertTrue(M.good(R, 10, s))


def random_op(rng, s, txs):
    """state-aware random legal operation, biased toward the happy path so traces reach the bank"""
    people = [AG, AG2, AP, AD, 5, GATE]
    ident = rng.randrange(max(1, s.next + 1))
    k = rng.randrange(17)
    if k < 3:
        return M.request(rng.choice(people) if rng.random() < .3 else rng.choice([AG, AG2]), rng.choice(txs))
    if k < 6:
        r = M.req_of(s, ident)
        tx = r.tx if (r is not None and rng.random() < .7) else rng.choice(txs)
        return M.approve(rng.choice(people) if rng.random() < .3 else AP, ident, tx)
    if k < 9:
        return M.execute(rng.choice(people), ident)
    if k < 12:
        return M.deliver(rng.choice(s.reserved) if s.reserved and rng.random() < .7 else ident)
    if k < 13:
        return M.bankCall(rng.choice([AG, AP, AD, 5]), ident, rng.choice(txs))
    if k < 16:
        keys = [m[0] for m in s.net]
        return M.arrive(rng.choice(keys) if keys and rng.random() < .8 else ident)
    return M.halt(rng.choice(people)) if rng.random() < .15 else M.deliver(ident)


def random_trace(rng, n, R=R, cap=10**9):
    """a random legal trace generated against the full-check model"""
    txs = [(rng.randrange(3), rng.randrange(1, 6), rng.randrange(2)) for _ in range(3)]
    s, ops = M.INIT, []
    for _ in range(n):
        o = random_op(rng, s, txs)
        ops.append(o)
        s = M.step(R, cap, M.FULL, s, o)
    return ops


class RandomTraces(unittest.TestCase):
    def test_inv_preserved(self):
        rng = random.Random(26)
        effects = 0
        for _ in range(2000):
            cap = rng.randrange(25)
            s = M.INIT
            for o in random_trace(rng, rng.randrange(1, 60), R, cap):
                self.assertTrue(M.legal(R, o))
                t = M.step(R, cap, M.FULL, s, o)
                self.assertEqual((t != s), M.guard(R, cap, M.FULL, s, o) and t != s)
                self.assertEqual(M.inv(R, cap, t), [], (s, o, t))
                s = t
            self.assertTrue(M.good(R, cap, s))
            self.assertTrue(M.once(s))
            effects += len(s.bank)
        self.assertGreater(effects, 150)  # non-vacuity: random traces do reach the bank

    def test_sound_checks_preserve_inv(self):
        """Lean `run_inv`/`safe_of_sound`: any Sound checks (nonce and haltCheck free) keep Inv and Good;
        `good_without_nonce` is the nonce-off instance"""
        rng = random.Random(27)
        nonce_effects = 0
        for i in range(2000):
            cap = rng.randrange(25)
            C = M.FULL._replace(nonce=bool(i % 2) and rng.random() < .5, haltCheck=rng.random() < .5)
            if i % 2 == 0:
                C = C._replace(nonce=False)
            self.assertTrue(M.sound(C))
            s = M.INIT
            for o in random_trace(rng, rng.randrange(1, 60), R, cap):
                s = M.step(R, cap, C, s, o)
                self.assertEqual(M.inv(R, cap, s), [], (C, o, s))
            self.assertTrue(M.good(R, cap, s))
            if not C.nonce:
                nonce_effects += len(s.bank)
        self.assertGreater(nonce_effects, 50)


if __name__ == "__main__":
    unittest.main(verbosity=2)
