#!/usr/bin/env python3
"""SC-08 trust-boundary negative witness, NOT a rerun of PREREG-SC08-EXEC-v1.

The reference launcher owns 0700 pin-dir and 0400 pinned script files, but
run_sc08.py launches the broker and agent as the same Unix UID. These mode
bits do not isolate one process from another process running as their owner.

The pinned script is passed to an interpreter by *pathname* after the digest
check, so modifying it between the check and interpreter open would defeat
the intended loaded-script/checked-digest identity. This test shows the
permission boundary is insufficient; it does not establish that the frozen
harness was exploited or that any deployment is vulnerable.
"""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


@unittest.skipUnless(os.name == "posix" and hasattr(os, "getuid"), "requires Unix ownership semantics")
class PinIsolationWitness(unittest.TestCase):
    def test_same_uid_peer_can_replace_read_only_pinned_script(self):
        with tempfile.TemporaryDirectory(prefix="sc08-pin-negative-") as dirname:
            pin_dir = Path(dirname) / "launcher-pins"
            pin_dir.mkdir(mode=0o700)
            pin = pin_dir / "checked.py"
            checked = b"print('approved')\n"
            substituted = b"print('different bytes')\n"
            pin.write_bytes(checked)
            pin.chmod(0o400)

            # This is the state at the trusted broker's successful digest check.
            self.assertEqual(pin.read_bytes(), checked)
            self.assertEqual(pin.stat().st_mode & 0o777, 0o400)

            # A same-UID peer (the untrusted side in this control) owns the file
            # under POSIX DAC, and may restore owner write permission itself.
            code = (
                "import os,pathlib; "
                "p=pathlib.Path(os.environ['SC08_PIN']); "
                "assert os.getuid()==int(os.environ['SC08_UID']); "
                "p.chmod(0o600); "
                "p.write_bytes(b\"print('different bytes')\\n\")"
            )
            env = dict(os.environ, SC08_PIN=str(pin), SC08_UID=str(os.getuid()))
            subprocess.run([sys.executable, "-c", code], check=True, env=env,
                           stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=10)

            # An interpreter opening the *path* now reads unapproved bytes.
            # This is not a trusted launcher exploit demonstration: the
            # adversarial peer must first have that same-UID filesystem access.
            self.assertEqual(pin.read_bytes(), substituted)
            self.assertNotEqual(pin.read_bytes(), checked)


if __name__ == "__main__":
    unittest.main()
