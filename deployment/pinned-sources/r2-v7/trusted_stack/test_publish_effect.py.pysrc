"""Linux real-file effect: non-execution, replay, revocation and HALT."""
import sqlite3
import concurrent.futures
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.server import run_one
from trusted_stack.publisher import publish_effect

AGENT, REVIEWER, APPROVER, ADMIN = 101, 201, 301, 401

class PublishEffectTests(unittest.TestCase):
    def setUp(self):
        t = tempfile.TemporaryDirectory()
        self.addCleanup(t.cleanup)
        base = Path(t.name)
        self.root = base / "effects"
        self.root.mkdir(mode=0o700)
        self.c = Controller.bootstrap(base / "trusted.db",
            Principals(frozenset({AGENT}), frozenset({REVIEWER}),
                       frozenset({APPROVER}), frozenset({ADMIN})),
            2, lambda: 100)
        self.body = b"reviewed-byte-string\0not-a-program"
        d = self.c.stage(AGENT, self.body)
        self.c.review(REVIEWER, d)
        self.c.issue_lease(ADMIN, "lease", AGENT, 2, 200)
        self.c.approve(APPROVER, "nonce", d, "logical/purpose", AGENT, "lease", 150)
        self.release_id = run_one(self.c, AGENT, dict(op="effect_release",
            nonce="nonce", digest=d, destination="logical/purpose", lease_id="lease"))
        self.target = self.root / f"effect-{self.release_id:012d}.bin"

    def publish(self):
        return run_one(self.c, ADMIN, dict(op="publish_effect", release_id=self.release_id),
                       effect_root=self.root)

    def test_commit_and_replay_exactly_one_file(self):
        got = self.publish()
        self.assertEqual(got["file"], self.target.name)
        self.assertEqual(self.target.read_bytes(), self.body)
        self.assertEqual(self.publish(), got)
        self.assertEqual(len(list(self.root.iterdir())), 1)
        self.assertEqual(self.c.state(ADMIN)["spent"], 1)

    def test_parallel_admin_retries_do_not_duplicate_external_effect(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            futures = [pool.submit(self.publish) for _ in range(12)]
            results = [f.result() for f in futures]
        self.assertEqual(len({result["file"] for result in results}), 1)
        self.assertEqual([p.name for p in self.root.iterdir()], [self.target.name])
        self.assertEqual(self.target.read_bytes(), self.body)
        self.assertEqual(self.c.state(ADMIN)["spent"], 1)

    def test_no_agent_or_unconfigured_publish(self):
        with self.assertRaises(Denied):
            run_one(self.c, AGENT, dict(op="publish_effect", release_id=self.release_id),
                    effect_root=self.root)
        with self.assertRaises(Denied):
            run_one(self.c, ADMIN, dict(op="publish_effect", release_id=self.release_id))
        for bad in (-1, True, "1", 0):
            with self.subTest(bad=bad), self.assertRaises(Denied):
                publish_effect(self.c, ADMIN, bad, self.root)
        self.assertFalse(self.target.exists())

    def test_no_pending_outbox_after_halt(self):
        self.c.halt(ADMIN)
        with self.assertRaises(Denied):
            self.publish()
        self.assertFalse(self.target.exists())

    def test_revocation(self):
        self.c.revoke(ADMIN, "lease")
        with self.assertRaises(Denied):
            self.publish()
        self.assertFalse(self.target.exists())

    def test_root_and_symlink_attack_fail_closed(self):
        alias = self.root.parent / "alias"
        alias.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(Denied):
            publish_effect(self.c, ADMIN, self.release_id, alias)
        self.root.chmod(0o777)
        with self.assertRaises(Denied):
            self.publish()
        self.root.chmod(0o700)
        self.assertFalse(self.target.exists())

    def test_existing_conflict_does_not_replace(self):
        self.target.write_bytes(b"collision")
        with self.assertRaises(Denied):
            self.publish()
        self.assertEqual(self.target.read_bytes(), b"collision")
        self.target.unlink()
        self.target.symlink_to(self.c.path)
        with self.assertRaises(Denied):
            self.publish()
        self.assertTrue(self.target.is_symlink())

    def test_outbox_survives_transient_file_failure(self):
        with patch("trusted_stack.publisher.os.link", side_effect=OSError("disk")):
            with self.assertRaises(Denied):
                self.publish()
        self.assertFalse(self.target.exists())
        self.assertEqual(self.c.state(ADMIN)["spent"], 1)
        self.publish()
        self.assertEqual(self.target.read_bytes(), self.body)

    def test_corrupted_db_bytes_no_external_effect(self):
        with sqlite3.connect(self.c.path) as db:
            db.execute("UPDATE effect_records SET body=? WHERE release_id=?",
                       (b"forged", self.release_id))
        with self.assertRaises(Denied):
            self.publish()
        self.assertFalse(self.target.exists())

    def test_crash_retry_uses_existing_file(self):
        self.publish()
        with patch("trusted_stack.publisher.os.link",
                   side_effect=AssertionError("should not relink")):
            self.publish()
        self.assertEqual(self.target.read_bytes(), self.body)

if __name__ == "__main__":
    unittest.main()
