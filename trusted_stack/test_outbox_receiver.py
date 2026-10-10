"""Real local-file publication, durable nonce and HALT ordering tests."""
import os
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


class LocalReceiverTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.db = base / "gate.db"
        self.out = base / "effects"
        self.out.mkdir(mode=0o700)
        admin = os.geteuid()
        self.agent, self.reviewer, self.approver = admin+10001, admin+10002, admin+10003
        self.roles = Principals(
            frozenset({self.agent}), frozenset({self.reviewer}),
            frozenset({self.approver}), frozenset({admin}))
        self.c = Controller.bootstrap(self.db, self.roles, 2, lambda: 100)
        self.body = b"reviewed\x00local-file-effect"
        self.digest = self.c.stage(self.agent, self.body)
        self.c.review(self.reviewer, self.digest)
        self.c.issue_lease(admin, "lease", self.agent, 2, 200)
        self.c.approve(self.approver, "nonce", self.digest, "label/not-path",
                       self.agent, "lease", 150)

    def admit(self):
        return self.c.release(self.agent, "nonce", self.digest,
                              "label/not-path", "lease", record_effect=True)

    def receipts(self):
        with sqlite3.connect(self.db) as con:
            try:
                return con.execute("SELECT * FROM delivery_receipts").fetchall()
            except sqlite3.OperationalError:
                return []

    def test_atomic_content_persists_restart_and_never_duplicates(self):
        release_id = self.admit()
        self.assertEqual(deliver_record(self.c, release_id, self.out), "1.body")
        self.assertEqual((self.out / "1.body").read_bytes(), self.body)
        self.assertEqual(self.receipts(), [(1, self.digest, "label/not-path")])
        reopened = Controller(self.db, self.roles, lambda: 100)
        self.assertEqual(deliver_record(reopened, release_id, self.out), "1.body")
        self.assertEqual(len(list(self.out.glob("*.body"))), 1)
        self.assertEqual(reopened.state(os.geteuid())["spent"], 1)

    def test_crash_after_publish_before_receipt_reconciles(self):
        release_id = self.admit()
        def die():
            raise RuntimeError("simulated killed process after durable publish")
        with self.assertRaises(RuntimeError):
            deliver_record(self.c, release_id, self.out, after_publish=die)
        self.assertEqual((self.out / "1.body").read_bytes(), self.body)
        self.assertEqual(self.receipts(), [])
        self.assertEqual(deliver_record(self.c, release_id, self.out), "1.body")
        self.assertEqual(len(self.receipts()), 1)

    def test_halt_serialization_and_no_post_halt_delivery(self):
        release_id = self.admit()
        self.c.halt(os.geteuid())
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)
        self.assertFalse((self.out / "1.body").exists())

    def test_halt_after_published_crash_cannot_undo_past_effect(self):
        release_id = self.admit()
        with self.assertRaises(RuntimeError):
            deliver_record(self.c, release_id, self.out,
                           after_publish=lambda: (_ for _ in ()).throw(RuntimeError()))
        self.c.halt(os.geteuid())
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)
        self.assertEqual((self.out / "1.body").read_bytes(), self.body)
        self.assertEqual(self.receipts(), [])

    def test_uncommitted_replay_and_corrupt_receiver_refused(self):
        with self.assertRaises(Denied):
            deliver_record(self.c, 1, self.out)
        release_id = self.admit()
        (self.out / "1.body").write_bytes(b"forged")
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)
        self.assertEqual((self.out / "1.body").read_bytes(), b"forged")
        self.assertEqual(self.receipts(), [])

    def test_no_symlink_or_world_writable_receiver(self):
        release_id = self.admit()
        (self.out / "1.body").symlink_to(self.db)
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)
        (self.out / "1.body").unlink()
        self.out.chmod(0o777)
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)
        self.out.chmod(0o700)
        self.assertEqual(self.receipts(), [])

    def test_missing_persisted_file_fails_closed(self):
        release_id = self.admit()
        deliver_record(self.c, release_id, self.out)
        (self.out / "1.body").unlink()
        with self.assertRaises(Denied):
            deliver_record(self.c, release_id, self.out)

    def test_no_agent_delivery_and_strict_identifier(self):
        with self.assertRaises(Denied):
            deliver_record(self.c, True, self.out)
        with self.assertRaises(Denied):
            deliver_record(self.c, -1, self.out)
        with self.assertRaises(Denied):
            deliver_record(self.c, 1, self.out, after_publish=lambda: None)
        # No unauthenticated 'deliver' RPC exists in trusted_stack.server.


if __name__ == "__main__":
    unittest.main()
