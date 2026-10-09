#!/usr/bin/env python3
"""Independent SC-10 restart-gap regression witness.

Runs the frozen reference store.py unchanged in an isolated temporary Unix-socket
directory, never with elevated privileges. This is a *negative* observation:
after a restart the append-only disk log survives but the store's in-memory
policy versions are empty. It is not a replay of preregistered evidence, nor a
claim that a deployment is unsafe without its broader environment assumptions.

Run: python3 -m unittest tools.test_sc10_restart_gap -v
"""
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import time
import unittest

REPO = Path(__file__).resolve().parents[1]
STORE = REPO / "scenarios" / "SC-10" / "harness" / "store.py"


def rpc(path: Path, msg: dict, timeout: float = 2.0) -> dict:
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.settimeout(timeout)
        s.connect(str(path))
        f = s.makefile("rwb")
        try:
            f.write((json.dumps(msg) + "\n").encode())
            f.flush()
            line = f.readline()
            if not line:
                raise AssertionError("store returned no reply")
            return json.loads(line)
        finally:
            f.close()


class StoreRestartGap(unittest.TestCase):
    def test_log_persists_but_active_versions_reset(self):
        if not sys.platform.startswith("linux") or not hasattr(socket, "SO_PEERCRED"):
            self.skipTest("SO_PEERCRED Linux-only reference model")
        self.assertTrue(STORE.is_file(), "SC-10 frozen store source not found")
        with tempfile.TemporaryDirectory(prefix="sc10-restart-gap-") as tmp:
            root = Path(tmp)
            log = root / "policy.jsonl"
            procs = []

            def launch():
                for role in ("write", "read"):
                    (root / f"{role}.sock").unlink(missing_ok=True)
                p = subprocess.Popen(
                    [sys.executable, "-B", str(STORE),
                     "--dir", str(root), "--admin-pid", str(os.getpid()),
                     "--log", str(log), "--lifetime", "12"],
                    stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                )
                procs.append(p)
                deadline = time.monotonic() + 4
                while time.monotonic() < deadline:
                    if p.poll() is not None:
                        raise AssertionError(
                            f"store exited early: {p.stderr.read().decode(errors='replace')}")
                    if (root / "write.sock").exists() and (root / "read.sock").exists():
                        try:
                            rpc(root / "read.sock", {"op": "latest"}, timeout=.3)
                            return p
                        except (OSError, TimeoutError):
                            pass
                    time.sleep(.03)
                raise AssertionError("store sockets did not become ready")

            try:
                first = launch()
                written = rpc(root / "write.sock", {
                    "op": "write", "policy": {"allow": ["example.invalid"]}})
                self.assertEqual(written.get("ok"), True, written)
                latest = rpc(root / "read.sock", {"op": "latest"})
                self.assertEqual(latest.get("version"), 0, latest)
                self.assertEqual(latest.get("policy"), {"allow": ["example.invalid"]})
                persisted = log.read_bytes()
                self.assertIn(b'"version": 0', persisted)
                first.terminate()
                first.wait(timeout=4)

                second = launch()
                after = rpc(root / "read.sock", {"op": "latest"})
                self.assertEqual(after.get("ok"), False, after)
                self.assertEqual(after.get("error"), "no policy", after)
                self.assertTrue(log.exists())
                self.assertEqual(log.read_bytes(), persisted)
                second.terminate()
                second.wait(timeout=4)
            finally:
                for p in procs:
                    if p.poll() is None:
                        p.terminate()
                        try:
                            p.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            p.kill()
                            p.wait(timeout=3)
                    if p.stderr is not None:
                        p.stderr.close()


if __name__ == "__main__":
    unittest.main()
