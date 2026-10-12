#!/usr/bin/env python3
"""The fast-tier skip helper must skip only after a green run on identical inputs, and never otherwise."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import ci_skip_unchanged as skip


class SkipTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo";self.root.mkdir();self.cache = Path(self.tmp.name) / "cache"
        (self.root / "a.lean").write_text("one");(self.root / "sub").mkdir();(self.root / "sub/b.lean").write_text("two")
        self.marker = self.root / "ran.txt"
    def run_check(self, command=None, patterns=("**/*.lean",), name="c", extra=()):
        command = command or [sys.executable, "-c", f"open({str(self.marker)!r},'a').write('x')"]
        return skip.main(["--name", name, "--inputs", *patterns, "--cache-dir", str(self.cache), "--root", str(self.root), *extra, "--", *command])
    def runs(self):return self.marker.read_text().count("x") if self.marker.exists() else 0
    def test_first_run_executes_then_unchanged_inputs_skip(self):
        self.assertEqual(self.run_check(), 0);self.assertEqual(self.runs(), 1)
        self.assertEqual(self.run_check(), 0);self.assertEqual(self.runs(), 1, "unchanged inputs must skip")
    def test_any_changed_matching_file_reruns(self):
        self.run_check();(self.root / "sub/b.lean").write_text("TWO");self.run_check();self.assertEqual(self.runs(), 2)
        (self.root / "sub/c.lean").write_text("new");self.run_check();self.assertEqual(self.runs(), 3)
        (self.root / "sub/c.lean").unlink();self.run_check();self.assertEqual(self.runs(), 4, "a deleted input is a change")
    def test_unrelated_file_does_not_rerun(self):
        self.run_check();(self.root / "notes.md").write_text("docs");self.run_check();self.assertEqual(self.runs(), 1)
    def test_failure_is_never_recorded(self):
        fail = [sys.executable, "-c", f"open({str(self.marker)!r},'a').write('x');raise SystemExit(3)"]
        self.assertEqual(self.run_check(fail), 3);self.assertEqual(self.run_check(fail), 3);self.assertEqual(self.runs(), 2)
    def test_command_change_or_force_reruns(self):
        self.run_check();self.run_check(extra=["--force"]);self.assertEqual(self.runs(), 2)
        other = [sys.executable, "-c", f"open({str(self.marker)!r},'a').write('x');pass"]
        self.run_check(other);self.assertEqual(self.runs(), 3, "a different command is a different check")
    def test_names_are_independent(self):
        self.run_check(name="one");self.run_check(name="two");self.assertEqual(self.runs(), 2)

if __name__ == "__main__":
    unittest.main()
