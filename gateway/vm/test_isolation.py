"""Configuration rejection controls, with no guest/channel experiments."""
from __future__ import annotations

import copy
import argparse
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from datetime import datetime, timezone

from check_isolation import IsolationError, check, validate_paths
from provision import sha

HERE = Path(__file__).resolve().parent
BASE = json.loads((HERE / "configs/local-20261008-final.json").read_text())
RECEIPT = json.loads((HERE / "receipts/qemu-provision-20261008-final.json").read_text())
LINKED = json.loads((HERE / "receipts/qemu-provision-20261008-linkfix.json").read_text())
ERRORS = {"shared-disk": "shared_file", "shared-9p": "shared_filesystem",
          "shared-virtiofs": "shared_filesystem", "shared-memory": "shared_memory",
          "second-network-path": "network_paths", "overlapping-cpu-pinning": "cpu_overlap",
          "hidden-config-include": "unknown_config"}


class IsolationControls(unittest.TestCase):
    def test_saved_positive_configuration_and_live_snapshot(self):
        self.assertEqual(check(BASE, RECEIPT)["configuration_check"], "pass")

    def test_every_resource_fixture_fails_library_and_cli(self):
        for name, code in ERRORS.items():
            with self.subTest(fixture=name):
                path = HERE / "fixtures" / (name + ".json")
                fixture = json.loads(path.read_text())
                with self.assertRaises(IsolationError) as caught:
                    check(fixture)
                self.assertEqual(caught.exception.code, code)
                result = subprocess.run([sys.executable, str(HERE / "check_isolation.py"),
                                         "--config", str(path)], capture_output=True, text=True)
                self.assertEqual(result.returncode, 1)
                self.assertIn(code + ":", result.stderr)

    def test_hardlink_and_symlink_aliases_fail(self):
        with tempfile.TemporaryDirectory() as work:
            a, b = Path(work) / "a", Path(work) / "b"
            a.write_bytes(b"private disk")
            b.hardlink_to(a)
            with self.assertRaises(IsolationError):
                validate_paths([a, b], True)
            b.unlink()
            b.symlink_to(a)
            with self.assertRaises(IsolationError):
                validate_paths([a, b], True)

    def test_stale_live_configuration_fails(self):
        r = copy.deepcopy(RECEIPT)
        r["live"]["VM-B"]["actual_argv"].extend(["-netdev", "user,id=extra"])
        with self.assertRaises(IsolationError) as caught:
            check(BASE, r)
        self.assertEqual(caught.exception.code, "live_config")

    def test_live_cpu_overlap_fails(self):
        r = copy.deepcopy(RECEIPT)
        for tid in r["live"]["VM-B"]["thread_cpu_affinity"]:
            r["live"]["VM-B"]["thread_cpu_affinity"][tid] = [0]
        with self.assertRaises(IsolationError) as caught:
            check(BASE, r)
        self.assertEqual(caught.exception.code, "cpu_overlap")

    def test_same_guest_boot_identity_fails(self):
        r = copy.deepcopy(RECEIPT)
        r["live"]["VM-B"]["guest"]["boot_id"] = r["live"]["VM-A"]["guest"]["boot_id"]
        with self.assertRaises(IsolationError) as caught:
            check(BASE, r)
        self.assertEqual(caught.exception.code, "guest_kernel")

    def test_link_fix_receipt_passes(self):
        self.assertEqual(check(BASE, LINKED)["configuration_check"], "pass")

    def test_extra_link_peer_fails(self):
        r = copy.deepcopy(LINKED)
        r["link"]["host_sockets_now"] += [["0100007F:4BC9", "0100007F:C000", "01"], ["0100007F:C000", "0100007F:4BC9", "01"]]
        with self.assertRaises(IsolationError) as caught:
            check(BASE, r)
        self.assertEqual(caught.exception.code, "network_paths")

    def test_missing_link_fails(self):
        r = copy.deepcopy(LINKED)
        r["link"]["host_sockets_at_start"] = [row for row in r["link"]["host_sockets_at_start"] if row[2] != "01"]
        with self.assertRaises(IsolationError) as caught:
            check(BASE, r)
        self.assertEqual(caught.exception.code, "network_paths")

    def test_enabled_ram_merging_fails(self):
        c = copy.deepcopy(BASE)
        c["vms"][0]["qemu_argv"] = [arg.replace("merge=off", "merge=on") for arg in c["vms"][0]["qemu_argv"]]
        with self.assertRaises(IsolationError) as caught:
            check(c)
        self.assertEqual(caught.exception.code, "shared_memory")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    if args.receipt and args.receipt.exists():
        raise SystemExit("refusing to overwrite control receipt")
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(IsolationControls))
    if args.receipt:
        paths = [HERE / "check_isolation.py", HERE / "provision.py", Path(__file__),
                 HERE / "configs/local-20261008-final.json", HERE / "receipts/qemu-provision-20261008-final.json",
                 *sorted((HERE / "fixtures").glob("*.json"))]
        args.receipt.write_text(json.dumps({"captured_at": datetime.now(timezone.utc).isoformat(),
            "status": "pass" if result.wasSuccessful() else "fail", "tests_run": result.testsRun,
            "resource_fixtures": ERRORS, "failures": len(result.failures), "errors": len(result.errors),
            "hashes": {str(p.relative_to(HERE)): sha(p) for p in paths}}, indent=2) + "\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)
