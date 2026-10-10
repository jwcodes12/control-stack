"""Separate-process CLI keeps untrusted roles out of real local dispatch."""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Principals


class DeliveryCLITests(unittest.TestCase):
    def test_separate_process_and_role_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)
            output = path / "out"
            output.mkdir(mode=0o700)
            uid = os.geteuid()
            roles = Principals(frozenset({uid + 15101}), frozenset({uid + 15102}),
                               frozenset({uid + 15103}), frozenset({uid}))
            db = path / "gate.db"
            controller = Controller.bootstrap(db, roles, 2, lambda: 100)
            body = b"reviewed\x00subprocess"
            digest = controller.stage(uid + 15101, body)
            controller.review(uid + 15102, digest)
            controller.issue_lease(uid, "lease", uid + 15101, 2, 200)
            controller.approve(uid + 15103, "nonce", digest, "label",
                               uid + 15101, "lease", 150)
            controller.release(uid + 15101, "nonce", digest, "label", "lease",
                               record_effect=True)
            args = [sys.executable, "-m", "trusted_stack.deliver_cli",
                    "--db", str(db), "--out", str(output), "--release-id", "1",
                    "--agents", str(uid + 15101), "--reviewers", str(uid + 15102),
                    "--approvers", str(uid + 15103), "--admins", str(uid)]
            # The test controller uses a fake clock; the CLI correctly uses
            # real time so the already expired lease is REJECTED.
            expired = subprocess.run(args, capture_output=True, text=True)
            self.assertNotEqual(expired.returncode, 0)
            self.assertFalse((output / "1.body").exists())
            # A production-valid approval needs a genuine clock. Test role
            # denial independently, before opening or delivering the DB.
            impostor = args[:]
            impostor[-1] = str(uid + 15104)
            denied = subprocess.run(impostor, capture_output=True, text=True)
            self.assertNotEqual(denied.returncode, 0)
            self.assertEqual(denied.stderr.strip(), "DENIED")


if __name__ == "__main__":
    unittest.main()
