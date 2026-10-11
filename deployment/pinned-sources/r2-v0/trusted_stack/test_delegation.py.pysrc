"""Authenticated, single-hop, exact-nonce agent delegation: hostile cases."""
import concurrent.futures
import os
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record
from trusted_stack.server import run_one


class DelegatedReleaseTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.out = self.root / "effects"
        self.out.mkdir(mode=0o700)
        admin = os.geteuid()
        self.a, self.b, self.c = (admin + 52001, admin + 52002, admin + 52003)
        self.reviewer, self.approver, self.admin = admin + 52004, admin + 52005, admin
        p = Principals(frozenset({self.a, self.b, self.c}),
                       frozenset({self.reviewer}),
                       frozenset({self.approver}), frozenset({self.admin}))
        self.db = self.root / "state.db"
        self.gate = Controller.bootstrap(self.db, p, 2, clock=lambda: 100)
        self.body = b"exact reviewed delegated\x00bytes"
        self.digest = self.gate.stage(self.a, self.body)
        self.gate.review(self.reviewer, self.digest)
        self.gate.issue_lease(self.admin, "lease-a", self.a, 2, 200)
        self.gate.approve(self.approver, "nonce-a", self.digest, "safe/label",
                          self.a, "lease-a", 150)
        self.request = {"op": "effect_release", "nonce": "nonce-a",
                        "digest": self.digest, "destination": "safe/label",
                        "lease_id": "lease-a"}

    def grant(self, uid=None, peer=None, nonce="nonce-a"):
        return run_one(self.gate, self.a if uid is None else uid,
                       {"op": "delegate", "nonce": nonce,
                        "delegate_uid": self.b if peer is None else peer})

    def release(self, uid):
        return run_one(self.gate, uid, self.request)

    def test_owner_grant_peer_provenance_and_durable_exact_bytes(self):
        with self.assertRaises(Denied):
            self.release(self.b)
        self.assertTrue(self.grant())
        with self.assertRaises(Denied):
            self.release(self.a)  # a delegated nonce cannot be reclaimed
        with self.assertRaises(Denied):
            self.release(self.c)
        rid = self.release(self.b)
        with sqlite3.connect(self.db) as con:
            self.assertEqual(con.execute(
                "SELECT agent_uid FROM releases WHERE id=?", (rid,)).fetchone(), (self.a,))
            self.assertEqual(con.execute(
                "SELECT nonce,grantor_uid,delegate_uid FROM delegated_releases WHERE release_id=?",
                (rid,)).fetchone(), ("nonce-a", self.a, self.b))
            self.assertEqual(con.execute("SELECT spent FROM meta").fetchone(), (1,))
        self.assertEqual(deliver_record(self.gate, rid, self.out), str(rid) + ".body")
        self.assertEqual((self.out / f"{rid}.body").read_bytes(), self.body)
        self.assertEqual(deliver_record(self.gate, rid, self.out), str(rid) + ".body")
        with self.assertRaises(Denied):
            self.release(self.b)

    def test_wrong_grantor_shape_transitive_and_double_grant_denied(self):
        with self.assertRaises(Denied):
            self.grant(uid=self.b)
        with self.assertRaises(Denied):
            self.grant(uid=self.approver)
        with self.assertRaises(Denied):
            self.grant(peer=self.a)
        with self.assertRaises(Denied):
            run_one(self.gate, self.a, {"op": "delegate", "nonce": "nonce-a",
                                       "delegate_uid": self.b, "agent_uid": self.a})
        self.grant()
        with self.assertRaises(Denied):
            self.grant(peer=self.c)  # immutable grant, cannot widen
        with self.assertRaises(Denied):
            self.grant(uid=self.b, peer=self.c)
        with self.assertRaises(Denied):
            run_one(self.gate, self.b, {**self.request, "agent_uid": self.a})
        self.assertEqual(self.gate.state(self.admin)["spent"], 0)

    def test_revocation_and_halt_block_pending_effect(self):
        self.grant()
        rid = self.release(self.b)
        with self.assertRaises(Denied):
            run_one(self.gate, self.c, {"op": "revoke_delegation", "nonce": "nonce-a"})
        self.assertTrue(run_one(self.gate, self.a,
                               {"op": "revoke_delegation", "nonce": "nonce-a"}))
        with self.assertRaises(Denied):
            deliver_record(self.gate, rid, self.out)
        self.assertEqual(list(self.out.glob("*.body")), [])
        self.assertEqual(self.gate.state(self.admin)["spent"], 1)
        self.gate.halt(self.admin)
        with self.assertRaises(Denied):
            self.grant()
        with self.assertRaises(Denied):
            deliver_record(self.gate, rid, self.out)

    def test_revocation_before_admission_prevents_delegate_and_owner(self):
        self.grant()
        run_one(self.gate, self.admin, {"op": "revoke_delegation", "nonce": "nonce-a"})
        for uid in (self.a, self.b, self.c):
            with self.assertRaises(Denied):
                self.release(uid)
        self.assertEqual(self.gate.state(self.admin)["spent"], 0)

    def test_simultaneous_replays_spend_global_budget_once(self):
        self.grant()
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
            futures = [pool.submit(self.release, uid)
                       for uid in ([self.a, self.b, self.c] * 10)]
        outcomes = []
        for future in futures:
            try:
                outcomes.append(future.result())
            except Denied:
                pass
        self.assertEqual(len(outcomes), 1)
        self.assertEqual(self.gate.state(self.admin)["spent"], 1)
        self.assertEqual(deliver_record(self.gate, outcomes[0], self.out),
                         str(outcomes[0]) + ".body")


if __name__ == "__main__":
    unittest.main()
