#!/usr/bin/env python3
"""Unit tests for the SC-12 trusted scheduler and cgctl bounds (no root, no cgroups: a fake cgroup layer)."""
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cgctl  # noqa: E402
from scheduler import Refused, Scheduler  # noqa: E402


class FakeProc:
    def __init__(self, pid):
        self.pid, self.stdout, self.returncode = pid, None, 0

    def poll(self):
        return 0

    def wait(self, timeout=None):
        return 0


class FakeCg:
    def __init__(self, root):
        self.root, self.launched, self.killed, self.n = Path(root), [], [], 1000

    def make(self, name, **kw):
        p = self.root / name
        p.mkdir()
        return p, kw

    def launch(self, path, uid, argv, stdout=None):
        self.n += 1
        self.launched.append({"path": str(path), "uid": uid, "argv": argv, "t": time.monotonic()})
        return FakeProc(self.n)

    def kill(self, path):
        self.killed.append((str(path), time.monotonic()))

    def cgpath(self, path):
        return str(path)


class SchedulerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cg = FakeCg(Path(self.tmp.name) / "cg")
        self.cg.root.mkdir()
        self.uid = os.getuid()

    def sched(self, claim=False):
        d = Path(self.tmp.name) / ("w%d" % len(os.listdir(self.tmp.name)))
        d.mkdir()
        s = Scheduler(self.cg, d, "/nonexistent/workloads.py", sys.executable, claim_mode=claim)
        self.addCleanup(s.close)
        return s

    def test_registration_uses_callers_session_and_ignores_claims(self):
        s = self.sched()
        s.start_session("A", self.uid)
        jid = s.register(self.uid, 5.0, claim="B")
        self.assertEqual(s.jobs[jid]["session"], "A")

    def test_claim_mode_honours_claim(self):
        s = self.sched(claim=True)
        s.start_session("A", self.uid)
        s.start_session("B", self.uid + 1 if self.uid == 0 else self.uid)
        jid = s.register(self.uid, 5.0, claim="B")
        self.assertEqual(s.jobs[jid]["session"], "B")

    def test_end_cancels_refuses_and_kills_once(self):
        s = self.sched()
        s.start_session("A", self.uid)
        jid = s.register(self.uid, 0.5)
        s.end("A")
        self.assertEqual(s.jobs[jid]["state"], "cancelled")
        with self.assertRaises(Refused):
            s.register(self.uid, 0.1)
        self.assertEqual(len(self.cg.killed), 1)
        time.sleep(0.7)
        self.assertEqual(self.cg.launched, [])  # the cancelled job never fires

    def test_due_job_fires_inside_session(self):
        s = self.sched()
        path = s.start_session("A", self.uid)
        s.register(self.uid, 0.05)
        time.sleep(0.3)
        self.assertEqual(len(self.cg.launched), 1)
        self.assertEqual(self.cg.launched[0]["path"], str(path))
        self.assertEqual(self.cg.launched[0]["uid"], self.uid)
        self.assertTrue(any(e["kind"] == "fire" for e in s.log))

    def test_no_launch_after_kill(self):
        # every fire launch happens before the session's kill (both take the scheduler lock)
        s = self.sched()
        s.start_session("A", self.uid)
        for d in (0.0, 0.01, 0.02, 0.03):
            s.register(self.uid, d)
        time.sleep(0.015)
        s.end("A")
        time.sleep(0.2)
        t_kill = self.cg.killed[0][1]
        self.assertTrue(all(x["t"] <= t_kill for x in self.cg.launched))


class BoundsTests(unittest.TestCase):
    def test_cg_refuses_bad_top_and_uids(self):
        with self.assertRaises(ValueError):
            cgctl.Cg("not-allowed", (23901,))
        with self.assertRaises(ValueError):
            cgctl.Cg("sc12-test", (1000,))

    def test_kill_uid_refuses_unreserved(self):
        with self.assertRaises(ValueError):
            cgctl.kill_uid(0, (23901,))


if __name__ == "__main__":
    unittest.main()
