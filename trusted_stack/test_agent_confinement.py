"""Host-kernel controls for a single one-shot Linux confined agent.

Test failures must not be converted to positive evidence. No simulation:
untrusted source calls real OS APIs with native ctypes available.
"""
import errno
import os
import platform
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from trusted_stack.agent_confinement import ConfinementUnavailable, capability_probe


class AgentConfinementTests(unittest.TestCase):
    def test_supported_host(self):
        if platform.system() != "Linux":
            self.skipTest("NO KERNEL EVIDENCE: Linux required")
        try:
            abi, lib = capability_probe()
        except ConfinementUnavailable as exc:
            self.skipTest("NO KERNEL EVIDENCE: " + str(exc))
        self.assertGreaterEqual(abi, 3)
        self.assertIsNotNone(lib)

    def test_host_denies_actual_writes_network_fork_and_metadata(self):
        if os.geteuid() == 0:
            self.skipTest("NO AGENT EVIDENCE: non-root test UID required")
        try:
            capability_probe()
        except ConfinementUnavailable as exc:
            self.skipTest("NO KERNEL EVIDENCE: " + str(exc))
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            victim = root / "victim"
            created = root / "created"
            scratch = root / "scratch"
            victim.write_bytes(b"unchanged")
            script = root / "agent.py"
            script.write_text(
                "import errno, os, socket, fcntl\n"
                f"victim={str(victim)!r}\n"
                f"created={str(created)!r}\n"
                f"scratch={str(scratch)!r}\n"
                "def denied(op):\n"
                "    try: op()\n"
                "    except OSError as e:\n"
                "        assert e.errno in (errno.EPERM, errno.EACCES), e\n"
                "        return\n"
                "    raise RuntimeError('BYPASS: unauthorized effect succeeded')\n"
                "denied(lambda: open(victim, 'wb').write(b'damaged'))\n"
                "denied(lambda: os.mkdir(created))\n"
                "denied(lambda: os.unlink(victim))\n"
                "denied(lambda: os.chmod(victim, 0o777))\n"
                "denied(lambda: socket.socket(socket.AF_INET, socket.SOCK_STREAM))\n"
                "denied(lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM))\n"
                "denied(lambda: os.fork())\n"
                "denied(lambda: fcntl.ioctl(3, 0))\n"
                "assert open(victim,'rb').read() == b'unchanged'\n"
                "assert not os.path.exists(created)\n"
                "assert not os.path.exists(scratch)\n",
                encoding="utf-8")
            cmd = [sys.executable, "-m", "trusted_stack.agent_confinement",
                   "--script", str(script)]
            completed = subprocess.run(
                cmd, cwd=Path(__file__).resolve().parents[1],
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                capture_output=True, timeout=45)
            self.assertEqual(completed.returncode, 0, completed.stderr.decode())
            self.assertEqual(victim.read_bytes(), b"unchanged")
            self.assertFalse(created.exists())

    def test_cannot_fall_back_to_unconfined_execution(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            marker = root / "bad"
            script = root / "bad.py"
            script.write_text(f"open({str(marker)!r}, 'wb').write(b'unsafe')\n")
            completed = subprocess.run(
                [sys.executable, "-m", "trusted_stack.agent_confinement",
                 "--script", str(script)],
                cwd=Path(__file__).resolve().parents[1],
                capture_output=True, timeout=45)
            self.assertNotEqual(completed.returncode, 0)
            self.assertFalse(marker.exists())


if __name__ == "__main__":
    unittest.main()
