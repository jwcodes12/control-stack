"""Bounded interleaving oracle for jointly committed admission and dispatch.

This is a reference integration test, NOT Lean-to-Python semantic refinement:
the oracle independently tracks expected accepted requests and local bytes.
"""
import itertools
import os
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


class JointTraceOracleTests(unittest.TestCase):
    def test_all_four_event_interleavings_and_halt_cut(self):
        for schedule in itertools.permutations(("agent-a", "agent-b", "deliver", "halt")):
            with self.subTest(schedule=schedule), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                receiver = root / "effect-root"
                receiver.mkdir(mode=0o700)
                owner = os.geteuid()
                agents = {"agent-a": owner + 24001, "agent-b": owner + 24002}
                reviewer, approver = owner + 24003, owner + 24004
                roles = Principals(frozenset(agents.values()),
                                   frozenset({reviewer}), frozenset({approver}),
                                   frozenset({owner}))
                db = root / "controller.db"
                gate = Controller.bootstrap(db, roles, global_cap=2, clock=lambda: 100)
                body = b"fixed-review\x00joint-runtime-test"
                digest = gate.stage(agents["agent-a"], body)
                gate.review(reviewer, digest)
                for name, uid in agents.items():
                    gate.issue_lease(owner, "lease-" + name, uid, 1, 200)
                    gate.approve(approver, "nonce-" + name, digest, "safe-label",
                                 uid, "lease-" + name, 150)

                halted = False
                admitted = []
                published = set()
                for event in schedule:
                    if event == "halt":
                        gate.halt(owner)
                        halted = True
                    elif event == "deliver":
                        for release_id in admitted:
                            if halted:
                                with self.assertRaises(Denied):
                                    deliver_record(gate, release_id, receiver)
                            else:
                                self.assertEqual(deliver_record(gate, release_id, receiver),
                                                 str(release_id) + ".body")
                                published.add(release_id)
                    else:
                        uid = agents[event]
                        if halted:
                            with self.assertRaises(Denied):
                                gate.release(uid, "nonce-" + event, digest, "safe-label",
                                             "lease-" + event, record_effect=True)
                        else:
                            release_id = gate.release(uid, "nonce-" + event, digest,
                                                      "safe-label", "lease-" + event,
                                                      record_effect=True)
                            admitted.append(release_id)

                    # Test oracle projects shared database state after EVERY
                    # schedule event, not just the final effect count.
                    snapshot = gate.state(owner)
                    self.assertEqual(snapshot["spent"], len(admitted))
                    self.assertEqual(snapshot["releases"], len(admitted))
                    self.assertEqual(snapshot["halted"], halted)
                    self.assertLessEqual(snapshot["spent"], 2)
                    with sqlite3.connect(db) as con:
                        self.assertEqual(
                            con.execute("SELECT COUNT(*) FROM effect_records").fetchone()[0],
                            len(admitted))
                        try:
                            receipts = con.execute(
                                "SELECT release_id FROM delivery_receipts").fetchall()
                        except sqlite3.OperationalError:
                            receipts = []
                    self.assertEqual({x[0] for x in receipts}, published)
                    actual = {int(p.stem) for p in receiver.glob("*.body")}
                    self.assertEqual(actual, published)
                    for release_id in published:
                        self.assertEqual((receiver / f"{release_id}.body").read_bytes(), body)

                # Even previously valid/replayed deliveries do not happen after
                # HALT, whereas earlier published files remain irreversible.
                for release_id in admitted:
                    with self.assertRaises(Denied):
                        deliver_record(gate, release_id, receiver)
                self.assertEqual(
                    {int(p.stem) for p in receiver.glob("*.body")}, published)


if __name__ == "__main__":
    unittest.main()
