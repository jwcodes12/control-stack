#!/usr/bin/env python3
"""Linux DAC negative control for the real local-file effect dispatcher.

Run via sudo -n on a disposable CI host. A process with a real different
kernel UID must NOT be able to dispatch a committed effect, even if it
forges --admins on the CLI. This does not prove absence of other OS bypasses.
"""
import os
import sqlite3
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Principals


@unittest.skipUnless(sys.platform.startswith("linux") and os.geteuid() == 0,
                     "requires privileged disposable Linux test runner")
class LocalReceiverRealUIDTests(unittest.TestCase):
    def test_real_untrusted_uid_cannot_dispatch_by_spoofing_admin_flags(self):
        with tempfile.TemporaryDirectory(prefix="local-receiver-uid-") as tmp:
            root = Path(tmp)
            directory = root / "receiver"
            directory.mkdir(mode=0o700)
            db = root / "gate.db"
            # UID 65534/GID 65534 is used only as a deliberately
            # unprivileged child identity inside this disposable test.
            agent, reviewer, approver, owner = 65534, 65533, 65532, 0
            roles = Principals(frozenset({agent}), frozenset({reviewer}),
                               frozenset({approver}), frozenset({owner}))
            controller = Controller.bootstrap(db, roles, 1)
            body = b"real-uid-denied\x00trusted-publication"
            digest = controller.stage(agent, body)
            controller.review(reviewer, digest)
            expiry = int(time.time()) + 3600
            controller.issue_lease(owner, "uid-lease", agent, 1, expiry)
            controller.approve(approver, "uid-nonce", digest, "fixed/label",
                               agent, "uid-lease", expiry)
            release_id = controller.release(
                agent, "uid-nonce", digest, "fixed/label", "uid-lease",
                record_effect=True)
            # Expose the parent as traversable. The test must not succeed
            # trivially due solely to the temporary parent being mode 0700.
            root.chmod(0o711)
            args = [
                sys.executable, "-m", "trusted_stack.deliver_cli",
                "--db", str(db), "--out", str(directory),
                "--release-id", str(release_id),
                "--agents", str(agent), "--reviewers", str(reviewer),
                "--approvers", str(approver), "--admins", str(owner),
            ]
            forged = args[:]
            forged[-1] = str(agent)
            denied = subprocess.run(
                forged, capture_output=True, text=True, timeout=15,
                user=agent, group=agent, extra_groups=[])
            self.assertNotEqual(denied.returncode, 0, denied.stdout)
            self.assertFalse((directory / f"{release_id}.body").exists())
            # The kernel identity, not a caller-provided flag, must remain
            # authoritative when the caller lists the genuine admin too.
            denied = subprocess.run(
                args, capture_output=True, text=True, timeout=15,
                user=agent, group=agent, extra_groups=[])
            self.assertNotEqual(denied.returncode, 0, denied.stdout)
            self.assertFalse((directory / f"{release_id}.body").exists())
            with sqlite3.connect(db) as con:
                self.assertEqual(
                    con.execute("SELECT COUNT(*) FROM effect_records").fetchone(),
                    (1,))
                try:
                    receipts = con.execute(
                        "SELECT COUNT(*) FROM delivery_receipts").fetchone()[0]
                except sqlite3.OperationalError:
                    receipts = 0
                self.assertEqual(receipts, 0)
            accepted = subprocess.run(
                args, capture_output=True, text=True, timeout=15)
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            self.assertEqual((directory / f"{release_id}.body").read_bytes(), body)
            with sqlite3.connect(db) as con:
                self.assertEqual(
                    con.execute("SELECT COUNT(*) FROM delivery_receipts").fetchone(),
                    (1,))


if __name__ == "__main__":
    unittest.main()
