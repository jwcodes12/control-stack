#!/usr/bin/env python3
"""SC-08 supplementary kernel-sealed script regression; not preregistered evidence."""
import hashlib
import os
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


if __name__ == "__main__":
    unittest.main()
