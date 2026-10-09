#!/usr/bin/env python3
"""Unit tests (no root, no sockets): GateCore against an in-process AnchorStore, plus the reconciliation.
Run: python3 -B experiments/anti-rollback/harness/test_ar.py"""
import os
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import anchor  # noqa: E402
import gate  # noqa: E402
import run_ar  # noqa: E402
from gate import GateCore, Refused  # noqa: E402


class Env:
    def __init__(self, cap=100, anchor_enabled=True):
        self.d = tempfile.mkdtemp(prefix="ar-test-")
        for sub in ("anchor", "gate", "snaps"):
            os.mkdir(os.path.join(self.d, sub))
        self.db = os.path.join(self.d, "gate", "gate.sqlite3")
        self.eff = os.path.join(self.d, "effects.log")
        self.crash = os.path.join(self.d, "gate", "crash_at")
        self.cap, self.anchor_enabled = cap, anchor_enabled
        self.a = anchor.AnchorStore(os.path.join(self.d, "anchor"))
        self.g = self.open()

    def open(self):
        self.a = anchor.AnchorStore(os.path.join(self.d, "anchor"))  # reload: a crashed child may have moved it
        self.g = GateCore(self.db, self.eff, self.a, self.cap, self.anchor_enabled, self.crash)
        return self.g

    def snap(self, name):
        shutil.copyfile(self.db, os.path.join(self.d, "snaps", name))

    def restore(self, name):
        self.g.db.close()
        shutil.copyfile(os.path.join(self.d, "snaps", name), self.db)
        return self.open()

    def crash_spend(self, point, nonce, amount):
        with open(self.crash, "w") as f:
            f.write(point)
        self.g.db.close()
        pid = os.fork()
        if pid == 0:
            try:
                g = GateCore(self.db, self.eff, anchor.AnchorStore(os.path.join(self.d, "anchor")), self.cap,
                             self.anchor_enabled, self.crash)
                g.spend(nonce, amount)
            finally:
                os._exit(0)
        return os.waitstatus_to_exitcode(os.waitpid(pid, 0)[1])

    def effects(self):
        return run_ar.jl(self.eff)

    def anchor_log(self):
        return run_ar.jl(os.path.join(self.d, "anchor", "anchor.log"))

    def close(self):
        self.g.db.close()
        shutil.rmtree(self.d)


class T(unittest.TestCase):
    def setUp(self):
        self.e = Env()

    def tearDown(self):
        self.e.close()

    def fill(self, n, snaps=()):
        if 0 in snaps:
            self.e.snap("S0")
        for i in range(1, n + 1):
            self.assertEqual(self.e.g.spend("n%d" % i, 20)["version"], i)
            if i in snaps:
                self.e.snap("S%d" % i)

    def test_happy_path_and_refusals(self):
        self.fill(5)
        with self.assertRaisesRegex(Refused, "nonce already used"):
            self.e.g.spend("n3", 1)
        with self.assertRaisesRegex(Refused, "budget exceeded"):
            self.e.g.spend("x", 1)
        self.assertTrue(self.e.g.chain_ok())
        self.assertEqual(self.e.a.read()["version"], 5)
        rec = run_ar.reconcile(self.e.anchor_log(), self.e.effects(), 100)
        self.assertTrue(rec["ok"], rec)

    def test_restore_older_fails_closed(self):
        for snap in ("S0", "S3", "S4"):
            e = Env()
            try:
                for i in range(1, 6):
                    if i == 1:
                        e.snap("S0")
                    e.g.spend("n%d" % i, 20)
                    if i in (3, 4):
                        e.snap("S%d" % i)
                g = e.restore(snap)
                self.assertEqual(g.status, "rollback")
                for n in ("n4", "f1", "n5"):
                    with self.assertRaisesRegex(Refused, "fail closed"):
                        g.spend(n, 20)
                self.assertEqual(len(e.effects()), 5)
                self.assertEqual(e.a.read()["version"], 5)
            finally:
                e.close()

    def test_deleted_store_fails_closed(self):
        self.fill(2)
        self.e.g.db.close()
        os.unlink(self.e.db)
        self.assertEqual(self.e.open().status, "rollback")

    def test_fork_detected_by_digest(self):
        """same version, different history: restore S3, crash-commit a different op 4 ... the anchor holds d4"""
        self.fill(3, snaps=(3,))
        self.e.crash_spend("after_commit", "n4a", 20)       # store 4a, anchor 3
        self.e.restore("S3")                               # store 3 == anchor 3: ok, 4a lost (never effected)
        self.assertEqual(self.e.g.status, "ok")
        self.e.snap("S3b")
        self.e.g.spend("n4b", 20)                          # store and anchor at (4, d4b)
        self.e.g.db.close()
        # build the forked (4, d4a) store again by replaying 4a on S3b, then restore it
        shutil.copyfile(os.path.join(self.e.d, "snaps", "S3b"), self.e.db)
        g = GateCore(self.e.db, os.path.join(self.e.d, "operator-scratch.log"), self.e.a, 100, anchor_enabled=False)  # operator writes 4a, no anchor
        g.spend("n4a", 20)
        g.db.close()
        self.assertEqual(self.e.open().status, "rollback")
        self.assertEqual([x["nonce"] for x in self.e.effects()], ["n1", "n2", "n3", "n4b"])
        self.assertTrue(run_ar.reconcile(self.e.anchor_log(), self.e.effects(), 100)["ok"])

    def test_crash_points_recover(self):
        for point, kind in (("after_commit", "anchor_incremented"), ("after_anchor", "effect_reperformed"),
                            ("after_effect", None)):
            e = Env()
            try:
                for i in range(1, 4):
                    e.g.spend("n%d" % i, 20)
                self.assertEqual(e.crash_spend(point, "n4", 20), 17)
                g = e.open()
                self.assertEqual(g.status, "ok")
                self.assertEqual(g.recovered["kind"] if g.recovered else None, kind, point)
                self.assertEqual(e.a.read()["version"], 4)
                self.assertEqual([x["nonce"] for x in e.effects()], ["n1", "n2", "n3", "n4"])
                with self.assertRaisesRegex(Refused, "nonce already used"):
                    g.spend("n4", 20)
                g.spend("n5", 20)
                self.assertTrue(run_ar.reconcile(e.anchor_log(), e.effects(), 100)["ok"])
            finally:
                e.close()

    def test_crash_window_restore(self):
        self.fill(3, snaps=(2, 3))
        self.assertEqual(self.e.crash_spend("after_commit", "n4", 20), 17)
        self.assertEqual(self.e.restore("S3").status, "ok")        # pre-op snapshot: op lost, retry lands once
        self.assertEqual(self.e.g.spend("n4", 20)["version"], 4)
        self.assertEqual([x["nonce"] for x in self.e.effects()], ["n1", "n2", "n3", "n4"])
        e = Env()
        try:
            for i in range(1, 4):
                e.g.spend("n%d" % i, 20)
                if i == 2:
                    e.snap("S2")
            e.crash_spend("after_commit", "n4", 20)
            self.assertEqual(e.restore("S2").status, "rollback")    # older than the anchor: fail closed
        finally:
            e.close()

    def test_crash_window_recovery_needs_matching_predecessor(self):
        """store = anchor + 1 but its predecessor digest is not the anchored one: refuse"""
        self.fill(3, snaps=(3,))
        self.e.g.spend("n4", 20)                           # anchor (4, d4)
        self.e.g.db.close()
        shutil.copyfile(os.path.join(self.e.d, "snaps", "S3"), self.e.db)
        g = GateCore(self.e.db, os.path.join(self.e.d, "operator-scratch.log"), self.e.a, 100, anchor_enabled=False)
        g.spend("z4", 1)
        g.spend("z5", 1)                                   # forked store at version 5 = anchor + 1
        g.db.close()
        self.assertEqual(self.e.open().status, "rollback")
        self.assertEqual(self.e.a.read()["version"], 4)

    def test_tampered_chain_refused(self):
        self.fill(3)
        self.e.g.db.execute("UPDATE journal SET op=? WHERE version=2", ('{"amount": 1, "nonce": "n2"}',))
        self.e.g.db.close()
        self.assertEqual(self.e.open().status, "rollback")

    def test_negative_control_replays(self):
        e = Env(anchor_enabled=False)
        try:
            for i in range(1, 6):
                e.g.spend("n%d" % i, 20)
                if i == 3:
                    e.snap("S3")
            g = e.restore("S3")
            self.assertEqual(g.status, "ok")
            g.spend("n4", 20)
            g.spend("f1", 20)
            rec = run_ar.reconcile(None, e.effects(), 100)
            self.assertIn("duplicate_nonce", rec["violations"])
            self.assertIn("over_cap", rec["violations"])
        finally:
            e.close()

    def test_anchor_monotone(self):
        a = self.e.a
        for bad in (0, 2, -1, "1", 1.0):
            with self.assertRaises(anchor.Refused):
                a.increment(bad, "1" * 64)
        with self.assertRaises(anchor.Refused):
            a.increment(1, "short")
        a.increment(1, "1" * 64)
        self.assertEqual(anchor.AnchorStore(a.d).read(), {"version": 1, "digest": "1" * 64})

    def test_reconcile_flags(self):
        al = [{"version": 1, "digest": "a"}, {"version": 2, "digest": "b"}]
        ok = [{"version": 1, "digest": "a", "nonce": "x", "amount": 1},
              {"version": 2, "digest": "b", "nonce": "y", "amount": 1}]
        self.assertTrue(run_ar.reconcile(al, ok, 2)["ok"])
        self.assertIn("over_cap", run_ar.reconcile(al, ok, 1)["violations"])
        self.assertIn("anchored_version_without_exactly_one_effect", run_ar.reconcile(al, ok[:1], 9)["violations"])
        self.assertIn("anchored_version_without_exactly_one_effect", run_ar.reconcile(al, ok + ok[1:], 9)["violations"])
        dup = ok + [{"version": 3, "digest": "c", "nonce": "x", "amount": 1}]
        v = run_ar.reconcile(al, dup, 9)["violations"]
        self.assertIn("duplicate_nonce", v)
        self.assertIn("effect_not_anchored", v)
        self.assertIn("effect_versions_not_increasing", run_ar.reconcile(None, ok + ok[:1], 9)["violations"])
        self.assertIn("anchor_log_not_contiguous", run_ar.reconcile(al[1:], [], 9)["violations"])

    def test_h3_ops_reference(self):
        ref, acc = run_ar.Ledger(run_ar.H3_CAP), 0
        for n, amt in run_ar.h3_ops():
            if ref.accepts(n, amt):
                ref.apply(n, amt)
                acc += 1
        self.assertEqual(len(run_ar.h3_ops()) - acc, 2)
        self.assertLessEqual(ref.spent, run_ar.H3_CAP)


if __name__ == "__main__":
    unittest.main(verbosity=1)
