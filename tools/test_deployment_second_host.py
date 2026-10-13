#!/usr/bin/env python3
"""The archived second-Linux-host run (GitHub-hosted Ubuntu 24.04, x86-64, AppArmor) is rechecked from its raw files."""
import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / "deployment/runs/tier12-second-host/run3-ubuntu-24.04-x86_64"


class SecondHost(unittest.TestCase):
    def test_host_is_a_different_linux_setup_from_the_primary(self):
        host = (RUN / "host.txt").read_text()
        self.assertIn("x86_64", host)
        self.assertIn("Ubuntu 24.04", host)
        self.assertIn("apparmor", host)
        self.assertNotIn("selinux", host)
        self.assertIn("landlock", host)

    def test_all_five_hardened_cases_agreed_and_were_conditional(self):
        result = json.loads((RUN / "containers-hardened/result.json").read_text())
        self.assertEqual(sorted(result["cases"]), ["clean", "concurrent-cap1", "crash-retry", "drift-uid", "halt-inflight"])
        for name, case in result["cases"].items():
            self.assertTrue(case["agreement"], name)
            self.assertEqual(case["prediction"], "CONDITIONAL", name)

    def test_the_independent_container_run_checker_passes_on_the_archive(self):
        p = subprocess.run([sys.executable, "deployment/check_container_run.py", str(RUN / "containers-hardened")],
                           cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("PASS", p.stdout)

    def test_landlock_tests_passed_on_that_kernel(self):
        self.assertIn("landlock_abi=", (RUN / "landlock-probe.txt").read_text())
        self.assertIn("OK", (RUN / "test_agent_confinement_nonroot.txt").read_text())
        self.assertIn("PASS: real kernel-confined delegate", (RUN / "test_confined_effect_broker.txt").read_text())


if __name__ == "__main__":
    unittest.main()
