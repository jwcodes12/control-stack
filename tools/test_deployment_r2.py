#!/usr/bin/env python3
"""Replay real-container artifacts without Docker; reject actual-byte tampering."""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.check_container_run import check
ARCHIVE=ROOT/'deployment/runs/tier2/containers-final'
class R2EvidenceTests(unittest.TestCase):
    def test_independent_reconciliation_and_relocated_archive(self):
        check(ARCHIVE)
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'archive';shutil.copytree(ARCHIVE,copy);check(copy)
            (copy/'crash-retry/after-crash/sink/1.body').write_bytes(b'not approved')
            with self.assertRaises(AssertionError):check(copy)
    def test_nonregular_sink_artifact_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'archive';shutil.copytree(ARCHIVE,copy)
            (copy/'clean/final/sink/extra.body').symlink_to('1.body')
            with self.assertRaises(AssertionError):check(copy)
if __name__=='__main__':unittest.main()
