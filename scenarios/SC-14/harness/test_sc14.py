#!/usr/bin/env python3
"""Unit tests for the SC-14 trusted job controller (no root, no cgroups: fake cgroup files in a temp dir)."""
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cgctl  # noqa: E402
from jobs import JobCtl, Refused  # noqa: E402

MIB = 1024 * 1024
BUDGET = {"cpu_usec": 500000, "memory": 32 * MIB, "pids": 8, "rate_quota": 50000, "expiry_s": 0.0}


class FakeProc:
    stdout = None

    def poll(self):
        return None

    def wait(self, timeout=None):
        return 0


class FakeCg:
    def __init__(self, root):
        self.root, self.killed = Path(root), []

    def make(self, name, **kw):
        p = self.root / name
        p.mkdir()
        set_usage(p, 0, 1 * MIB, 1)
        return p, kw

    def launch(self, path, uid, argv, stdout=None):
        return FakeProc()

    def kill(self, path):
        self.killed.append(str(path))


def set_usage(p, usec, mem, pids):
    (p / "cpu.stat").write_text("usage_usec %d\nnr_throttled 0\n" % usec)
    (p / "memory.current").write_text(str(mem))
    (p / "pids.current").write_text(str(pids))


class JobCtlTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cg = FakeCg(self.tmp.name)
        self.ctl = JobCtl(self.cg)
        self.addCleanup(self.ctl.close)

    def wait_for(self, cond, t=1.0):
        t0 = time.monotonic()
        while time.monotonic() - t0 < t:
            if cond():
                return True
            time.sleep(0.01)
        return False

    def test_per_resource_cpu_budget_kills(self):
        j, _ = self.ctl.create("a", BUDGET)
        self.ctl.launch("a", 23905, ["x"])
        set_usage(j.path, 400000, MIB, 1)
        time.sleep(0.05)
        self.assertIsNone(j.killed)
        set_usage(j.path, 500001, MIB, 1)
        self.assertTrue(self.wait_for(lambda: j.killed is not None))
        self.assertEqual(j.killed["reason"], "cpu_budget")

    def test_aggregate_lets_one_resource_exceed(self):
        # aggregate_cap_breaks: CPU at 2x its own cap, the sum of fractions still <= 3
        j, _ = self.ctl.create("b", BUDGET, mode="aggregate", agg_cap=3.0)
        self.ctl.launch("b", 23905, ["x"])
        set_usage(j.path, 1000000, 4 * MIB, 1)  # 2.0 + 0.125 + 0.125
        time.sleep(0.1)
        self.assertIsNone(j.killed)
        set_usage(j.path, 1400000, 4 * MIB, 1)  # 2.8 + 0.25 > 3
        self.assertTrue(self.wait_for(lambda: j.killed is not None))
        self.assertEqual(j.killed["reason"], "aggregate")

    def test_expiry_kills_and_refuses(self):
        j, _ = self.ctl.create("c", dict(BUDGET, expiry_s=0.1))
        self.ctl.launch("c", 23905, ["x"])
        self.assertTrue(self.wait_for(lambda: j.killed is not None))
        self.assertEqual(j.killed["reason"], "expiry")
        self.assertLessEqual(j.killed["t"] - j.deadline, 0.05)
        with self.assertRaises(Refused):
            self.ctl.launch("c", 23905, ["x"])

    def test_bounds(self):
        with self.assertRaises(ValueError):
            cgctl.Cg("sc14-test", (23900,))


if __name__ == "__main__":
    unittest.main()
