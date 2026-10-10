"""Adversarial F8: concurrent independent leases and delegated in-flight effects.

All callers here are simulated identities at the Controller layer. The
separate Linux SO_PEERCRED test covers actual peer authentication. This is a
joint SQL/filesystem regression, not semantic proof of the host scheduler.
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


class DelegatedFleetTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self.dest = root / "out"
        self.dest.mkdir(mode=0o700)
        self.db = root / "trusted.db"
        self.admin = os.geteuid()
        self.a, self.b, self.c = (self.admin + i for i in (701, 702, 703))
        review, approver = self.admin + 704, self.admin + 705
        roles = Principals(frozenset({self.a, self.b, self.c}),
                           frozenset({review}), frozenset({approver}),
                           frozenset({self.admin}))
        self.gate = Controller.bootstrap(self.db, roles, 1, clock=lambda: 100)
        self.body = b"delegated-fleet-reviewed-body"
        digest = self.gate.stage(self.a, self.body)
        self.gate.review(review, digest)
        self.digest = digest
        self.gate.issue_lease(self.admin, "lease-a", self.a, 1, 200)
        self.gate.issue_lease(self.admin, "lease-c", self.c, 1, 200)
        self.gate.approve(approver, "nonce-a", digest, "reviewed/a",
                          self.a, "lease-a", 150)
        self.gate.approve(approver, "nonce-c", digest, "reviewed/c",
                          self.c, "lease-c", 150)

    def _attempt(self, which):
        if which == "delegate":
            return self.gate.release(self.b, "nonce-a", self.digest,
                                     "reviewed/a", "lease-a", record_effect=True)
        if which == "owner":
            return self.gate.release(self.a, "nonce-a", self.digest,
                                     "reviewed/a", "lease-a", record_effect=True)
        if which == "stranger":
            return self.gate.release(self.c, "nonce-a", self.digest,
                                     "reviewed/a", "lease-a", record_effect=True)
        assert which == "independent"
        return self.gate.release(self.c, "nonce-c", self.digest,
                                 "reviewed/c", "lease-c", record_effect=True)

    def test_global_cap_race_owner_grant_delegate_independent(self):
        self.gate.delegate(self.a, "nonce-a", self.b)
        attempts = ["delegate", "owner", "independent", "stranger"] * 16
        with concurrent.futures.ThreadPoolExecutor(max_workers=24) as pool:
            futures = [pool.submit(self._attempt, name) for name in attempts]
        good = []
        for f in futures:
            try:
                good.append(f.result())
            except Denied:
                pass
        self.assertEqual(len(good), 1)
        self.assertEqual(self.gate.state(self.admin)["spent"], 1)
        self.assertEqual(self.gate.state(self.admin)["releases"], 1)
        rid = good[0]
        with sqlite3.connect(self.db) as db:
            rows = db.execute("SELECT agent_uid,nonce FROM releases").fetchall()
            self.assertEqual(len(rows), 1)
            if rows[0][1] == "nonce-a":
                self.assertEqual(rows[0][0], self.a)
                self.assertEqual(db.execute(
                    "SELECT delegate_uid FROM delegated_releases WHERE release_id=?",
                    (rid,)).fetchone(), (self.b,))
            else:
                self.assertEqual(rows[0], (self.c, "nonce-c"))
            self.assertEqual(db.execute("SELECT SUM(used) FROM leases").fetchone(), (1,))
        self.assertEqual(deliver_record(self.gate, rid, self.dest), f"{rid}.body")
        self.assertEqual((self.dest / f"{rid}.body").read_bytes(), self.body)
        reopened = Controller(self.db, self.gate.principals, clock=lambda: 100)
        self.assertEqual(reopened.state(self.admin)["spent"], 1)
        with self.assertRaises(Denied):
            self._attempt("delegate")

    def test_grant_revocation_after_admission_fences_inflight_publication(self):
        self.gate.delegate(self.a, "nonce-a", self.b)
        rid = self._attempt("delegate")
        self.gate.revoke_delegation(self.a, "nonce-a")
        with self.assertRaises(Denied):
            deliver_record(self.gate, rid, self.dest)
        self.assertEqual(list(self.dest.iterdir()), [])
        self.assertEqual(self.gate.state(self.admin)["spent"], 1)
        with self.assertRaises(Denied):
            self._attempt("owner")

    def test_delegated_publication_then_fault_and_halt_never_unpublishes(self):
        self.gate.delegate(self.a, "nonce-a", self.b)
        rid = self._attempt("delegate")
        def injected_crash():
            raise RuntimeError("fault after durable publication")
        with self.assertRaises(RuntimeError):
            deliver_record(self.gate, rid, self.dest, after_publish=injected_crash)
        self.assertEqual((self.dest / f"{rid}.body").read_bytes(), self.body)
        self.gate.halt(self.admin)
        with self.assertRaises(Denied):
            deliver_record(self.gate, rid, self.dest)
        with sqlite3.connect(self.db) as db:
            present = db.execute("SELECT COUNT(*) FROM delivery_receipts").fetchone()
            self.assertEqual(present, (0,))

    def test_mutated_delegation_provenance_cannot_publish(self):
        self.gate.delegate(self.a, "nonce-a", self.b)
        rid = self._attempt("delegate")
        with sqlite3.connect(self.db) as db:
            db.execute("UPDATE delegated_releases SET delegate_uid=? WHERE release_id=?",
                       (self.c, rid))
        with self.assertRaises(Denied):
            deliver_record(self.gate, rid, self.dest)
        self.assertEqual(list(self.dest.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
