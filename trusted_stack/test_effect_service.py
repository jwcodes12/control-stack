"""Exact-byte SQLite reference effect, replay and crash-failure controls.

The effect under test is ONE SQLite record. No actual filesystem, process,
network, bank or VM action is performed or claimed here.
"""
import concurrent.futures
import hashlib
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.server import run_one

AGENT, REVIEWER, APPROVER, ADMIN = 101, 201, 301, 401


class EffectTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dbfile = Path(self.tmp.name) / "trusted.db"
        roles = Principals(frozenset({AGENT}), frozenset({REVIEWER}),
                           frozenset({APPROVER}), frozenset({ADMIN}))
        self.c = Controller.bootstrap(self.dbfile, roles, 3, lambda: 100)
        self.body = b"exact audited bytes\x00not executable"
        self.digest = self.c.stage(AGENT, self.body)
        self.c.review(REVIEWER, self.digest)
        self.c.issue_lease(ADMIN, "l1", AGENT, 2, 200)
        self.c.approve(APPROVER, "n1", self.digest, "specimen/a", AGENT, "l1", 150)

    def req(self, **changes):
        r = {"op": "effect_release", "nonce": "n1", "digest": self.digest,
             "destination": "specimen/a", "lease_id": "l1"}
        return run_one(self.c, AGENT, dict(r, **changes))

    def rows(self, table):
        with sqlite3.connect(self.dbfile) as db:
            return db.execute("SELECT * FROM " + table).fetchall()

    def test_exact_content_is_atomic_and_consumed_once(self):
        self.assertEqual(self.req(), 1)
        self.assertEqual(self.rows("effect_records")[0][4], self.body)
        self.assertEqual(self.rows("effect_records")[0][2], self.digest)
        self.assertEqual(self.rows("effect_records")[0][3], "specimen/a")
        self.assertEqual(self.c.state(ADMIN)["spent"], 1)
        self.assertEqual(len(self.rows("releases")), 1)
        with self.assertRaises(Denied):
            self.req()
        self.assertEqual(len(self.rows("effect_records")), 1)

    def test_rejected_requests_are_effect_free(self):
        for mutation in ({"nonce": "wrong"}, {"digest": hashlib.sha256(b"bad").hexdigest()},
                         {"destination": "specimen/other"}, {"lease_id": "wrong"},
                         {"cost": 2}, {"destination": "../bad"}):
            with self.subTest(mutation=mutation), self.assertRaises(Denied):
                self.req(**mutation)
        with self.assertRaises(Denied):
            run_one(self.c, APPROVER, {"op": "effect_release", "nonce": "n1",
                    "digest": self.digest, "destination": "specimen/a", "lease_id": "l1"})
        self.assertEqual(self.rows("effect_records"), [])
        self.assertEqual(self.c.state(ADMIN)["spent"], 0)

    def test_injected_effect_failure_rolls_back_approval_and_budget(self):
        with sqlite3.connect(self.dbfile) as db:
            db.executescript("""CREATE TRIGGER fail_effect BEFORE INSERT ON effect_records
                                BEGIN SELECT RAISE(ABORT, 'injected sink failure'); END;""")
        with self.assertRaises(Denied):
            self.req()
        self.assertEqual(self.rows("effect_records"), [])
        self.assertEqual(self.rows("releases"), [])
        self.assertEqual(self.c.state(ADMIN)["spent"], 0)
        self.assertEqual(self.rows("approvals")[0][-1], 0)
        with sqlite3.connect(self.dbfile) as db:
            db.execute("DROP TRIGGER fail_effect")
        self.assertEqual(self.req(), 1)

    def test_replay_races_have_one_effect(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
            fs = [pool.submit(self.req) for _ in range(20)]
        good = 0
        for f in fs:
            try:
                f.result()
                good += 1
            except Denied:
                pass
        self.assertEqual(good, 1)
        self.assertEqual(len(self.rows("effect_records")), 1)
        self.assertEqual(self.c.state(ADMIN)["spent"], 1)

    def test_halt_before_release_has_no_effect(self):
        self.c.halt(ADMIN)
        with self.assertRaises(Denied):
            self.req()
        self.assertEqual(self.rows("effect_records"), [])
        self.assertEqual(self.rows("releases"), [])


if __name__ == "__main__":
    unittest.main()
