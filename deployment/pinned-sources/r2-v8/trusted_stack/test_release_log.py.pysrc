"""Source generation r2-v8: persisted release log, observed-hash publication receipts, per-agent staging quota,
bounded receiver lock retry. The release_log tests mirror the facts proved for the Lean model in
ControlStack/Deployment/ReleaseLog.lean (log soundness, event-time facts, immutability after a review overwrite)."""
import hashlib
import os
import re
import sqlite3
import tempfile
import threading
import time
import unittest
from pathlib import Path

from trusted_stack import outbox_receiver
from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record

ROOT = Path(__file__).resolve().parents[1]


class Base(unittest.TestCase):
    CAP = 5

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.db = base / "gate.db"
        self.out = base / "effects"
        self.out.mkdir(mode=0o700)
        self.admin = os.geteuid()
        self.agent, self.agent2 = self.admin + 10001, self.admin + 10011
        self.rev1, self.rev2 = self.admin + 10002, self.admin + 10012
        self.approver = self.admin + 10003
        self.roles = Principals(frozenset({self.agent, self.agent2}), frozenset({self.rev1, self.rev2}),
                                frozenset({self.approver}), frozenset({self.admin}))
        self.now = 100
        self.c = Controller.bootstrap(self.db, self.roles, self.CAP, lambda: self.now)

    def sql(self, query, args=()):
        with sqlite3.connect(self.db) as con:
            return con.execute(query, args).fetchall()

    def admit(self, nonce, body, *, agent=None, lease=None, destination="label/x", record_effect=False, reviewer=None):
        agent = agent or self.agent
        lease = lease or ("lease-" + str(agent))
        digest = self.c.stage(agent, body)
        self.c.review(reviewer or self.rev1, digest)
        if not self.sql("SELECT 1 FROM leases WHERE lease_id=?", (lease,)):
            self.c.issue_lease(self.admin, lease, agent, 5, 1000)
        self.c.approve(self.approver, nonce, digest, destination, agent, lease, 500)
        return digest, self.c.release(agent, nonce, digest, destination, lease, record_effect=record_effect)


class ReleaseLogTests(Base):
    def test_row_records_the_admission_and_survives_a_review_overwrite(self):
        digest, rid = self.admit("n1", b"reviewed-bytes")
        row = self.sql("SELECT release_id,nonce,digest,destination,agent_uid,lease_id,signer_uid,reviewer_uid,cost FROM release_log")
        self.assertEqual(row, [(rid, "n1", digest, "label/x", self.agent, "lease-" + str(self.agent), self.approver, self.rev1, 1)])
        # The retained review entry can be replaced by another reviewer; the log keeps the release-time reviewer.
        self.c.review(self.rev2, digest)
        self.assertEqual(self.sql("SELECT reviewer_uid FROM reviews WHERE digest=?", (digest,)), [(self.rev2,)])
        self.assertEqual(self.sql("SELECT reviewer_uid FROM release_log"), [(self.rev1,)])

    def test_log_is_a_faithful_shadow_of_the_broker_counters(self):
        # Lean: LogSound = nonces equal the consumed history, costs sum to spent, length equals releases.
        for i in range(3):
            self.admit("n%d" % i, b"body-%d" % i)
        state = self.c.state(self.admin)
        log = self.sql("SELECT nonce,cost FROM release_log ORDER BY release_id")
        self.assertEqual(len(log), state["releases"])
        self.assertEqual(sum(c for _, c in log), state["spent"])
        self.assertEqual(len({n for n, _ in log}), len(log))
        self.assertEqual({n for n, _ in log}, {n for (n,) in self.sql("SELECT nonce FROM releases")})
        self.assertEqual(self.sql("SELECT COUNT(*) FROM approvals WHERE used=1"), [(len(log),)])

    def test_denied_requests_and_halt_write_no_row(self):
        digest, _ = self.admit("n1", b"x")
        with self.assertRaises(Denied):  # replay of the consumed nonce
            self.c.release(self.agent, "n1", digest, "label/x", "lease-" + str(self.agent))
        with self.assertRaises(Denied):  # unapproved nonce
            self.c.release(self.agent, "never-approved", digest, "label/x", "lease-" + str(self.agent))
        self.assertEqual(self.sql("SELECT COUNT(*) FROM release_log"), [(1,)])
        digest2 = self.c.stage(self.agent, b"y")
        self.c.review(self.rev1, digest2)
        self.c.approve(self.approver, "n2", digest2, "label/x", self.agent, "lease-" + str(self.agent), 500)
        self.c.halt(self.admin)
        with self.assertRaises(Denied):  # no new event after HALT
            self.c.release(self.agent, "n2", digest2, "label/x", "lease-" + str(self.agent))
        self.assertEqual(self.sql("SELECT COUNT(*) FROM release_log"), [(1,)])

    def test_release_log_is_append_only_for_sql_writers(self):
        self.admit("n1", b"x")
        with sqlite3.connect(self.db) as con:
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("UPDATE release_log SET digest='0'*64")
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("DELETE FROM release_log")
        self.assertEqual(self.sql("SELECT COUNT(*) FROM release_log"), [(1,)])

    def test_a_database_from_an_older_generation_is_upgraded_in_place(self):
        with sqlite3.connect(self.db) as con:
            for name in ("release_log_no_update", "release_log_no_delete"):
                con.execute("DROP TRIGGER " + name)
            con.execute("DROP TABLE release_log")
            con.execute("DROP TABLE artifact_owner")
        digest, rid = self.admit("n1", b"after-upgrade")
        self.assertEqual(self.sql("SELECT release_id,digest FROM release_log"), [(rid, digest)])
        with sqlite3.connect(self.db) as con, self.assertRaises(sqlite3.IntegrityError):
            con.execute("DELETE FROM release_log")

    def test_runtime_columns_correspond_to_the_lean_release_event_fields(self):
        source = (ROOT / "ControlStack/Deployment/ReleaseLog.lean").read_text()
        body = re.search(r"structure ReleaseEvent where\n((?:  \w+ : Nat\n)+)", source).group(1)
        lean_fields = {line.split(":")[0].strip() for line in body.splitlines()}
        columns = {r[1] for r in self.sql("PRAGMA table_info(release_log)")} - {"release_id", "created"}
        runtime = {re.sub(r"_(uid|id)$", "", c) for c in columns}
        self.assertEqual(lean_fields, runtime)


class PublicationReceiptTests(Base):
    def test_receipt_holds_the_hash_read_back_and_is_idempotent_and_append_only(self):
        digest, rid = self.admit("n1", b"bytes-on-disk", record_effect=True)
        self.assertEqual(deliver_record(self.c, rid, self.out), "%d.body" % rid)
        rows = self.sql("SELECT release_id,observed_sha256,destination FROM publication_receipts")
        self.assertEqual(rows, [(rid, hashlib.sha256((self.out / ("%d.body" % rid)).read_bytes()).hexdigest(), "label/x")])
        self.assertEqual(rows[0][1], digest)
        self.assertEqual(self.sql("SELECT digest FROM release_log"), [(digest,)])
        self.assertEqual(deliver_record(Controller(self.db, self.roles, lambda: self.now), rid, self.out), "%d.body" % rid)
        self.assertEqual(self.sql("SELECT COUNT(*) FROM publication_receipts"), [(1,)])
        with sqlite3.connect(self.db) as con:
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("UPDATE publication_receipts SET observed_sha256='0'*64")
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("DELETE FROM publication_receipts")

    def test_tampered_published_file_is_refused_not_re_receipted(self):
        _, rid = self.admit("n1", b"original", record_effect=True)
        deliver_record(self.c, rid, self.out)
        path = self.out / ("%d.body" % rid)
        path.chmod(0o600)
        path.write_bytes(b"changed")
        with self.assertRaises(Denied):
            deliver_record(self.c, rid, self.out)
        self.assertEqual(self.sql("SELECT COUNT(*) FROM publication_receipts"), [(1,)])


class StagingQuotaTests(Base):
    def setUp(self):
        super().setUp()
        self.c.STAGING_QUOTA = 10  # two agents: five bytes each

    def test_each_agent_has_its_own_share_and_cannot_starve_the_other(self):
        self.assertEqual(self.c.agent_quota(), 5)
        self.c.stage(self.agent, b"aaaaa")
        with self.assertRaisesRegex(Denied, "per-agent staging quota"):
            self.c.stage(self.agent, b"b")
        self.c.stage(self.agent2, b"ccccc")  # the other agent still has its whole share
        with self.assertRaisesRegex(Denied, "quota"):
            self.c.stage(self.agent2, b"d")
        self.assertEqual(self.c.stage(self.agent2, b"aaaaa"), hashlib.sha256(b"aaaaa").hexdigest())  # already staged: free

    def test_the_total_quota_still_applies(self):
        self.c.STAGING_QUOTA = 6
        self.assertEqual(self.c.agent_quota(), 3)
        self.c.stage(self.agent, b"aaa")
        self.c.stage(self.agent2, b"bbb")
        with self.assertRaisesRegex(Denied, "quota"):
            self.c.stage(self.agent, b"c")


class LockRetryTests(Base):
    def hold_writer_lock(self, seconds):
        ready = threading.Event()

        def hold():
            con = sqlite3.connect(self.db, isolation_level=None)
            con.execute("BEGIN IMMEDIATE")
            ready.set()
            time.sleep(seconds)
            con.execute("ROLLBACK")
            con.close()
        thread = threading.Thread(target=hold)
        thread.start()
        self.assertTrue(ready.wait(5))
        self.addCleanup(thread.join)

    def test_delivery_waits_out_a_busy_writer_instead_of_failing(self):
        _, rid = self.admit("n1", b"x", record_effect=True)
        self.c.BUSY_TIMEOUT = 0.05
        self.hold_writer_lock(1.2)
        self.assertEqual(deliver_record(self.c, rid, self.out), "%d.body" % rid)

    def test_delivery_fails_closed_after_the_deadline(self):
        _, rid = self.admit("n1", b"x", record_effect=True)
        self.c.BUSY_TIMEOUT = 0.05
        old, outbox_receiver.LOCK_DEADLINE = outbox_receiver.LOCK_DEADLINE, 0.3
        self.addCleanup(setattr, outbox_receiver, "LOCK_DEADLINE", old)
        self.hold_writer_lock(1.5)
        with self.assertRaises(Denied):
            deliver_record(self.c, rid, self.out)
        self.assertFalse((self.out / ("%d.body" % rid)).exists())


if __name__ == "__main__":
    unittest.main()
