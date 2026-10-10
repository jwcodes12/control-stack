"""Two-agent concurrent release and real local receiver integration."""
import concurrent.futures
import os
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


class ReceiverJointTests(unittest.TestCase):
    def test_shared_budget_lease_and_halt_serialization(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            directory = root / "published"
            directory.mkdir(mode=0o700)
            owner = os.geteuid()
            agents = (owner + 30101, owner + 30102)
            reviewer, approver = owner + 30103, owner + 30104
            roles = Principals(frozenset(agents), frozenset({reviewer}),
                               frozenset({approver}), frozenset({owner}))
            dbfile = root / "gate.db"
            controller = Controller.bootstrap(dbfile, roles, 3, lambda: 100)
            body = b"globally capped\x00two-agent-body"
            digest = controller.stage(agents[0], body)
            controller.review(reviewer, digest)
            work = []
            for i, agent in enumerate(agents):
                lease = "lease" + str(i)
                controller.issue_lease(owner, lease, agent, 2, 200)
                for j in range(2):
                    nonce = "nonce" + str(i) + str(j)
                    controller.approve(approver, nonce, digest, "safe/label",
                                       agent, lease, 150)
                    work.append((agent, nonce, lease))

            def attempt(args):
                agent, nonce, lease = args
                try:
                    return controller.release(agent, nonce, digest, "safe/label",
                                              lease, cost=1, record_effect=True)
                except Denied:
                    return None

            with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
                ids = list(pool.map(attempt, work))
            accepted = [x for x in ids if x is not None]
            self.assertEqual(len(accepted), 3)
            self.assertEqual(len(set(accepted)), 3)
            self.assertEqual(controller.state(owner)["spent"], 3)

            # Independent receiver calls race but serialize with the SQLite lock.
            with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
                results = list(pool.map(
                    lambda i: deliver_record(controller, i, directory),
                    accepted + accepted + accepted))
            self.assertEqual(sorted(set(results)), sorted(str(i) + ".body" for i in accepted))
            self.assertEqual(len(list(directory.glob("*.body"))), 3)
            self.assertTrue(all((directory / (str(i) + ".body")).read_bytes() == body
                                for i in accepted))
            with sqlite3.connect(dbfile) as db:
                self.assertEqual(db.execute("SELECT COUNT(*) FROM delivery_receipts").fetchone(), (3,))
                self.assertEqual(db.execute("SELECT COUNT(*) FROM effect_records").fetchone(), (3,))
                self.assertEqual(db.execute("SELECT SUM(used) FROM leases").fetchone(), (3,))
            controller.halt(owner)
            with self.assertRaises(Denied):
                deliver_record(controller, accepted[0], directory)
            self.assertEqual(controller.state(owner)["spent"], 3)


if __name__ == "__main__":
    unittest.main()
