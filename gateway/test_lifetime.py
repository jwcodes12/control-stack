"""Concurrent admissions, restart/crash durability and fail-closed ledger controls."""
import concurrent.futures
import multiprocessing
import os
import sqlite3
import tempfile
import unittest
from contextlib import closing
from pathlib import Path

from gateway import Channel, Gateway, GatewayError, LifetimeLedger, Schema


def admission(args):
    path, bits, lineage, size = args
    return LifetimeLedger(Path(path), bits).charge(lineage, size)


def interrupted_charge(path, commit):
    db = sqlite3.connect(path)
    db.execute("PRAGMA synchronous=FULL")
    db.execute("BEGIN IMMEDIATE")
    db.execute("UPDATE usage SET product='256', admissions=2 WHERE lineage='same-secret'")
    if commit:
        db.commit()
    os._exit(0)


class LifetimeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = Path(self.tmp.name) / "ledger.sqlite3"
        self.ledger = LifetimeLedger.create(self.path, 16)

    def tearDown(self):
        self.tmp.cleanup()

    def test_concurrent_charges_never_exceed_budget(self):
        ctx = multiprocessing.get_context("spawn")
        with concurrent.futures.ProcessPoolExecutor(max_workers=8, mp_context=ctx) as pool:
            accepted = list(pool.map(admission, [(str(self.path), 16, "same-secret", 16)] * 24))
        self.assertEqual(sum(accepted), 4)
        self.assertEqual(self.ledger.usage("same-secret"), (65536, 4))
        self.assertFalse(LifetimeLedger(self.path, 16).charge("same-secret", 16))

    def test_restart_retains_spent_budget(self):
        self.assertTrue(self.ledger.charge("same-secret", 65536))
        self.assertFalse(LifetimeLedger(self.path, 16).charge("same-secret", 2))
        self.assertEqual(self.ledger.usage("same-secret"), (65536, 1))

    def test_process_crash_before_commit_rolls_back(self):
        self.ledger.charge("same-secret", 16)
        child = multiprocessing.get_context("spawn").Process(target=interrupted_charge, args=(str(self.path), False))
        child.start(); child.join(10)
        self.assertEqual(child.exitcode, 0)
        self.assertEqual(self.ledger.usage("same-secret"), (16, 1))

    def test_process_exit_after_commit_retains_charge(self):
        self.ledger.charge("same-secret", 16)
        child = multiprocessing.get_context("spawn").Process(target=interrupted_charge, args=(str(self.path), True))
        child.start(); child.join(10)
        self.assertEqual(child.exitcode, 0)
        self.assertEqual(self.ledger.usage("same-secret"), (256, 2))

    def test_missing_state_never_resets_usage(self):
        self.ledger.charge("same-secret", 65536)
        self.path.unlink()
        with self.assertRaises(GatewayError):
            self.ledger.charge("same-secret", 2)
        with self.assertRaises(GatewayError):
            LifetimeLedger(self.path, 16)
        self.assertFalse(self.path.exists())

    def test_corrupt_or_wrong_configuration_is_rejected(self):
        with self.assertRaises(GatewayError):
            LifetimeLedger(self.path, 15)
        with self.assertRaises(GatewayError):
            LifetimeLedger.create(self.path, 16)
        self.path.write_bytes(b"corrupt")
        with self.assertRaises(GatewayError):
            self.ledger.charge("same-secret", 2)

    def test_invalid_usage_cannot_reduce_charge(self):
        self.ledger.charge("same-secret", 16)
        with closing(sqlite3.connect(str(self.path))) as db, db:
            db.execute("UPDATE usage SET product='0' WHERE lineage='same-secret'")
        with self.assertRaises(GatewayError):
            self.ledger.charge("same-secret", 16)

    def test_invalid_sizes_and_lineages_are_rejected(self):
        for size in [0, -1, True, 1.5, "2"]:
            with self.assertRaises(GatewayError):
                self.ledger.charge("same-secret", size)
        for lineage in [None, "", 7, "x" * 201]:
            with self.assertRaises(GatewayError):
                self.ledger.charge(lineage, 2)
        self.assertEqual(self.ledger.usage("same-secret"), (1, 0))

    def test_certified_gateway_requires_ledger_and_lineage(self):
        ch = {"repair": Channel("repair", Schema((("id", tuple(range(8))),)), 1)}
        for kwargs in [{}, {"ledger": self.ledger}, {"ledger": self.ledger, "lineage": ""}]:
            with self.assertRaises(GatewayError):
                Gateway(ch, require_lifetime=True, **kwargs)
        for _ in range(5):
            Gateway(ch, ledger=self.ledger, lineage="same-secret", require_lifetime=True)
        with self.assertRaises(GatewayError):
            Gateway(ch, ledger=self.ledger, lineage="same-secret", require_lifetime=True)
        self.assertEqual(self.ledger.usage("same-secret"), (9 ** 5, 5))

    def test_symlink_state_is_rejected(self):
        other = self.path.with_name("alias.sqlite3")
        other.symlink_to(self.path)
        with self.assertRaises(GatewayError):
            LifetimeLedger(other, 16)


if __name__ == "__main__":
    unittest.main()
