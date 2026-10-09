#!/usr/bin/env python3
"""SC-08 supplementary kernel-sealed script regression; not preregistered evidence."""
import hashlib
import json
import os
import socket
import tempfile
import threading
import time
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scenarios" / "SC-08" / "harness"))
from sealed_script import sealed_script_fd, verified_script_path, _requirements, SealedScriptUnavailable


class SealedScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            _requirements()
        except SealedScriptUnavailable as exc:
            raise unittest.SkipTest(str(exc))
        if not os.path.isdir("/proc/self/fd"):
            raise unittest.SkipTest("Linux /proc/self/fd unavailable")

    def test_exec_consumes_sealed_original_bytes(self):
        data = b"import hashlib, pathlib; print(hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())\n"
        fd = sealed_script_fd(data)
        try:
            self.assertTrue(os.get_inheritable(fd))
            res = subprocess.run(
                [sys.executable, "-I", "-S", "-B", verified_script_path(fd)],
                pass_fds=[fd], capture_output=True, text=True, timeout=10, check=True)
            self.assertEqual(res.stdout.strip(), hashlib.sha256(data).hexdigest())
        finally:
            os.close(fd)

    def test_same_uid_cannot_mutate_after_seal(self):
        data = b"print('approved')\n"
        fd = sealed_script_fd(data)
        try:
            self.assertEqual(os.read(fd, len(data) + 1), data)
            with self.assertRaises(OSError):
                os.write(fd, b"poison")
            other = (
                "import os,sys; "
                "path=sys.argv[1]; "
                "fd=os.open(path,os.O_WRONLY); "
                "os.write(fd,b'poison')"
            )
            # Reopening may itself fail, or the write must fail.
            child = subprocess.run([sys.executable, "-c", other,
                                    "/proc/%d/fd/%d" % (os.getpid(), fd)],
                                   capture_output=True, text=True, timeout=10)
            self.assertNotEqual(child.returncode, 0)
            os.lseek(fd, 0, os.SEEK_SET)
            self.assertEqual(os.read(fd, len(data) + 1), data)
        finally:
            os.close(fd)

    def test_rejects_wrong_source_type(self):
        with self.assertRaises(TypeError):
            sealed_script_fd("untrusted string")


    def test_launcher_opt_in_sealed_mode_resists_source_path_swap(self):
        launcher = Path(__file__).resolve().parents[1] / "scenarios" / "SC-08" / "harness" / "launcher.py"
        with tempfile.TemporaryDirectory(prefix="sc08-sealed-") as directory:
            d = Path(directory)
            origin = d / "source.py"
            approved = (b"import hashlib, os\n"
                        b"b=open(__file__,'rb').read()\n"
                        b"open(os.environ['SC08_SENTINEL'],'a').write(hashlib.sha256(b).hexdigest()+'\\n')\n"
                        b"print('approved-script')\n")
            origin.write_bytes(approved)
            binary = os.path.realpath(sys.executable)
            allow = {
                "interpreters": [hashlib.sha256(Path(binary).read_bytes()).hexdigest()],
                "scripts": [hashlib.sha256(approved).hexdigest()]
            }
            (d / "allow.json").write_text(json.dumps(allow))
            argv = [sys.executable, "-I", "-S", "-B", str(launcher),
                    "--dir", str(d), "--allowlist", str(d / "allow.json"),
                    "--pin-dir", str(d / "pins"), "--out", str(d / "output"),
                    "--sentinel", str(d / "sentinel"), "--log", str(d / "log"),
                    "--sealed-script", "--check-exec-delay", "0.7", "--lifetime", "15"]
            service = subprocess.Popen(argv, stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True)
            try:
                self.assertTrue(service.stdout.readline().startswith("READY "))
                result = {}
                def request():
                    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as conn:
                        conn.settimeout(10)
                        conn.connect(str(d / "agent.sock"))
                        fh = conn.makefile("rwb")
                        fh.write((json.dumps({"op": "run", "program": binary,
                                              "script": str(origin)}) + "\n").encode())
                        fh.flush()
                        result.update(json.loads(fh.readline()))
                worker = threading.Thread(target=request)
                worker.start()
                time.sleep(0.25)
                t_swap = time.monotonic_ns()
                origin.write_bytes(b"print('substituted')\n")
                worker.join(timeout=12)
                self.assertFalse(worker.is_alive())
                self.assertEqual(result.get("decision"), "executed", result)
                self.assertEqual(result.get("rc"), 0, result)
                self.assertTrue(result.get("executed_path", "").startswith("/proc/self/fd/"))
                self.assertLess(result["t_check"], t_swap)
                self.assertLess(t_swap, result["t_exec"])
                self.assertEqual((d / "sentinel").read_text().strip(),
                                 hashlib.sha256(approved).hexdigest())
                self.assertIn("approved-script", (d / "output").read_text())
                self.assertNotIn("substituted", (d / "output").read_text())
            finally:
                if service.poll() is None:
                    service.terminate()
                try:
                    service.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    service.kill()
                    service.communicate(timeout=5)


if __name__ == "__main__":
    unittest.main()
