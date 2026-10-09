#!/usr/bin/env python3
"""Unit fixtures for bank.py at the dispatch level (no sockets, no root): authentication, idempotency, and the
`conflict` answer to a repeated key with a different payload (unreachable through the gate, so tested directly)."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bank import Bank  # noqa: E402
from common import Refused  # noqa: E402

GATE, AGENT, AUDITOR = 23605, 23601, 23607


def tr(key, amount=5, dest=7, memo=1):
    return {"op": "transfer", "key": key, "dest": dest, "amount": amount, "memo": memo}


class BankFixtures(unittest.TestCase):
    def mk(self, disabled=()):
        self.td = tempfile.TemporaryDirectory()
        return Bank(str(Path(self.td.name) / "b.sqlite3"), GATE, AUDITOR, disabled)

    def tearDown(self):
        self.td.cleanup()

    def test_idempotent_and_conflict(self):
        b = self.mk()
        self.assertEqual(b.dispatch(GATE, tr(1)), "applied")
        self.assertEqual(b.dispatch(GATE, tr(1)), "duplicate")
        self.assertEqual(b.dispatch(GATE, tr(1, amount=6)), "conflict")
        led = b.dispatch(AUDITOR, {"op": "ledger"})
        self.assertEqual([(e["key"], e["amount"]) for e in led], [(1, 5)])
        acc = b.dispatch(AUDITOR, {"op": "access"})
        self.assertEqual([a["outcome"] for a in acc], ["applied", "duplicate", "conflict"])

    def test_auth(self):
        b = self.mk()
        with self.assertRaises(Refused):
            b.dispatch(AGENT, tr(1))
        with self.assertRaises(Refused):
            b.dispatch(AGENT, {"op": "ledger"})
        self.assertEqual(b.dispatch(AUDITOR, {"op": "ledger"}), [])

    def test_controls(self):
        b = self.mk(("dedup",))
        b.dispatch(GATE, tr(1))
        self.assertEqual(b.dispatch(GATE, tr(1, amount=6)), "applied")
        self.assertEqual(len(b.dispatch(AUDITOR, {"op": "ledger"})), 2)
        self.td.cleanup()
        b = self.mk(("auth",))
        self.assertEqual(b.dispatch(AGENT, tr(2)), "applied")


if __name__ == "__main__":
    unittest.main(verbosity=2)
