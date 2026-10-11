"""Safety-shaped negative controls: reference gate + concurrent admission.

Tests call Controller directly with *simulated* trusted UID identities.
Only the separate broker process can use real SO_PEERCRED authentication.
"""
import concurrent.futures
import hashlib
import tempfile
import threading
import unittest
from pathlib import Path
from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.server import run_one

AGENT, REVIEWER, APPROVER, ADMIN, OTHER = 1001, 1002, 1003, 1004, 1005


class GateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / "db.sqlite3"
        self.principals = Principals(frozenset({AGENT}), frozenset({REVIEWER}),
                                     frozenset({APPROVER}), frozenset({ADMIN}))
        self.now = 1000
        self.gate = Controller.bootstrap(self.path, self.principals, 5, lambda: self.now)
        self.body = b"reviewed specimen, not executable"
        self.digest = self.gate.stage(AGENT, self.body)
        self.gate.review(REVIEWER, self.digest)
        self.gate.issue_lease(ADMIN, "lease1", AGENT, 3, 1200)
        self.gate.approve(APPROVER, "nonce1", self.digest, "staging/one",
                          AGENT, "lease1", 1100)

    def request(self, nonce="nonce1", digest=None, destination="staging/one",
                lease_id="lease1", cost=1, agent=AGENT):
        return self.gate.release(agent, nonce, digest or self.digest, destination, lease_id, cost)

    def test_atomic_release_bound_and_nonce(self):
        self.assertEqual(self.request(), 1)
        with self.assertRaises(Denied):
            self.request()
        self.assertEqual(self.gate.state(ADMIN)["spent"], 1)
        self.assertEqual(self.gate.state(ADMIN)["releases"], 1)
        self.assertEqual(self.gate.stage(AGENT, self.body), self.digest)

    def test_tamper_and_agent_privilege_escalation(self):
        other_digest = hashlib.sha256(b"evil").hexdigest()
        for mutation in ({"digest": other_digest}, {"destination": "staging/two"},
                         {"lease_id": "other"}, {"cost": 0}, {"cost": True},
                         {"destination": "../etc/passwd"}, {"agent": OTHER}):
            with self.subTest(mutation=mutation), self.assertRaises(Denied):
                self.request(**mutation)
        with self.assertRaises(Denied):
            self.gate.review(AGENT, self.digest)
        with self.assertRaises(Denied):
            self.gate.approve(AGENT, "nonce2", self.digest, "staging/x", AGENT, "lease1", 1100)
        with self.assertRaises(Denied):
            self.gate.issue_lease(AGENT, "other", AGENT, 5, 1100)
        with self.assertRaises(Denied):
            self.gate.halt(AGENT)
        self.assertEqual(self.gate.state(ADMIN)["releases"], 0)

    def test_revocation_and_expirations(self):
        self.gate.revoke(ADMIN, "lease1")
        with self.assertRaises(Denied):
            self.request()
        self.assertEqual(self.gate.state(ADMIN)["releases"], 0)

    def test_approval_deadline(self):
        self.now = 1100
        with self.assertRaises(Denied):
            self.request()

    def test_lease_expiry(self):
        self.now = 1200
        with self.assertRaises(Denied):
            self.request()

    def test_halt_absorbs_and_survives_reopen(self):
        self.gate.halt(ADMIN)
        Controller(self.path, self.principals, lambda: self.now)
        for action in (lambda: self.request(), lambda: self.gate.stage(AGENT, b"other"),
                       lambda: self.gate.review(REVIEWER, self.digest),
                       lambda: self.gate.issue_lease(ADMIN, "x", AGENT, 1, 1400)):
            with self.assertRaises(Denied):
                action()
        self.assertTrue(self.gate.state(ADMIN)["halted"])
        self.assertTrue(self.gate.halt(ADMIN))

    def test_global_and_per_lease_shared_budgets(self):
        self.assertEqual(self.request(cost=3), 1)
        self.gate.issue_lease(ADMIN, "lease2", AGENT, 4, 1200)
        self.gate.approve(APPROVER, "nonce2", self.digest, "staging/two", AGENT, "lease2", 1100)
        with self.assertRaises(Denied):
            self.gate.release(AGENT, "nonce2", self.digest, "staging/two", "lease2", 3)
        self.assertEqual(self.gate.release(AGENT, "nonce2", self.digest, "staging/two", "lease2", 2), 2)
        self.assertEqual(self.gate.state(ADMIN)["spent"], 5)
        self.assertEqual(self.gate.state(ADMIN)["releases"], 2)

    def test_concurrent_replay_exactly_once(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
            futures = [pool.submit(self.request) for _ in range(20)]
        accepted = 0
        for future in futures:
            try:
                future.result()
                accepted += 1
            except Denied:
                pass
        self.assertEqual(accepted, 1)
        self.assertEqual(self.gate.state(ADMIN)["releases"], 1)
        self.assertEqual(self.gate.state(ADMIN)["spent"], 1)

    def test_restart_never_resets_counters(self):
        self.request()
        second = Controller(self.path, self.principals, lambda: self.now)
        self.assertEqual(second.state(ADMIN)["spent"], 1)
        with self.assertRaises(Denied):
            second.release(AGENT, "nonce1", self.digest, "staging/one", "lease1", 1)

    def test_fail_closed_corruption_missing_or_alias_state(self):
        extra = self.path.with_name("alias")
        extra.hardlink_to(self.path)
        with self.assertRaises(Denied):
            Controller(self.path, self.principals)
        extra.unlink()
        self.path.chmod(0o644)
        with self.assertRaises(Denied):
            Controller(self.path, self.principals)
        self.path.chmod(0o600)
        self.path.unlink()
        with self.assertRaises(Denied):
            Controller(self.path, self.principals)

    def test_authorization_shapes_and_halt_broker(self):
        self.assertEqual(run_one(self.gate, ADMIN, {"op": "state"})["spent"], 0)
        with self.assertRaises(Denied):
            run_one(self.gate, AGENT, {"op": "state", "uid": ADMIN})
        with self.assertRaises(Denied):
            run_one(self.gate, AGENT, {"op": "halt"})
        with self.assertRaises(Denied):
            run_one(self.gate, AGENT, {"op": "release", "nonce": "nonce1",
                        "digest": self.digest, "destination": "staging/one",
                        "lease_id": "lease1", "cost": 1, "uid": APPROVER})

    def test_nonce_must_not_be_reissued(self):
        with self.assertRaises(Denied):
            self.gate.approve(APPROVER, "nonce1", self.digest, "staging/two",
                              AGENT, "lease1", 1100)

    def test_unreviewed_or_missing_artifact_denied(self):
        digest = self.gate.stage(AGENT, b"unreviewed")
        with self.assertRaises(Denied):
            self.gate.approve(APPROVER, "nonce2", digest, "staging/evil",
                              AGENT, "lease1", 1100)

    def test_principal_disjointness_required(self):
        with self.assertRaises(ValueError):
            Principals(frozenset({1}), frozenset({1}), frozenset({2}), frozenset({3}))


if __name__ == "__main__":
    unittest.main()
