"""Deterministic live SQLite writer-lock / filesystem publication race controls.

Tests actual concurrent threads and real filesystem effects, rather than merely
enumerating abstract sequential schedules. These are source-side regressions;
they do not establish OS isolation, power-loss atomicity or Lean refinement.
"""
import concurrent.futures
import os
import sqlite3
import tempfile
import threading
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


class HaltDeliveryRaceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.output = root / "effect-output"
        self.output.mkdir(mode=0o700)
        owner = os.geteuid()
        agent, reviewer, approver = owner + 44101, owner + 44102, owner + 44103
        roles = Principals(frozenset({agent}), frozenset({reviewer}),
                           frozenset({approver}), frozenset({owner}))
        self.owner = owner
        self.dbpath = root / "gate.sqlite"
        self.gate = Controller.bootstrap(self.dbpath, roles, 1, lambda: 100)
        self.body = b"concurrent-halt\x00exact-reviewed-bytes"
        digest = self.gate.stage(agent, self.body)
        self.gate.review(reviewer, digest)
        self.gate.issue_lease(owner, "race-lease", agent, 1, 300)
        self.gate.approve(approver, "race-nonce", digest, "non-path-label",
                          agent, "race-lease", 250)
        self.release_id = self.gate.release(
            agent, "race-nonce", digest, "non-path-label", "race-lease",
            record_effect=True)

    def receipts(self):
        with sqlite3.connect(self.dbpath) as db:
            try:
                return db.execute(
                    "SELECT release_id, digest, destination FROM delivery_receipts"
                ).fetchall()
            except sqlite3.OperationalError:
                return []

    def run_race(self, *, crash_after_publish):
        published = threading.Event()
        let_finish = threading.Event()
        halt_invoked = threading.Event()

        def after_publish():
            # Callback occurs with BEGIN IMMEDIATE still held, and *after*
            # the actual file publication has been fsynced.
            published.set()
            if not let_finish.wait(timeout=10):
                raise AssertionError("halt/delivery test interleaving timed out")
            if crash_after_publish:
                raise RuntimeError("injected death before durable SQLite receipt")

        def stop():
            halt_invoked.set()
            return self.gate.halt(self.owner)

        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            delivery = pool.submit(
                deliver_record, self.gate, self.release_id,
                self.output, after_publish=after_publish)
            self.assertTrue(published.wait(timeout=10), "publication never reached")
            self.assertEqual(
                (self.output / f"{self.release_id}.body").read_bytes(), self.body)
            halting = pool.submit(stop)
            self.assertTrue(halt_invoked.wait(timeout=10), "HALT not scheduled")
            # The active delivery transaction must serialize before HALT.
            self.assertFalse(halting.done(), "HALT committed during publication")
            let_finish.set()
            if crash_after_publish:
                with self.assertRaises(RuntimeError):
                    delivery.result(timeout=10)
            else:
                self.assertEqual(delivery.result(timeout=10),
                                 f"{self.release_id}.body")
            self.assertTrue(halting.result(timeout=10))
        self.assertTrue(self.gate.state(self.owner)["halted"])
        with self.assertRaises(Denied):
            deliver_record(self.gate, self.release_id, self.output)
        self.assertEqual(
            (self.output / f"{self.release_id}.body").read_bytes(), self.body)
        self.assertEqual(len(list(self.output.glob("*.body"))), 1)
        return self.receipts()

    def test_halt_waits_until_external_publication_and_receipt_commit(self):
        rows = self.run_race(crash_after_publish=False)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0][0], self.release_id)
        self.assertEqual(rows[0][2], "non-path-label")

    def test_halt_after_published_crash_preserves_unreceipted_effect(self):
        # A crash after fsync but before SQLite COMMIT cannot be rolled back
        # by a later HALT. It must not be represented as zero external effects.
        self.assertEqual(self.run_race(crash_after_publish=True), [])


if __name__ == "__main__":
    unittest.main()
