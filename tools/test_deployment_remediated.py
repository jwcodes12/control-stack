#!/usr/bin/env python3
"""Archived positive evidence must reject byte and observation tampering."""
import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.check_remediated import check
ARCHIVE=ROOT/'deployment/runs/tier5/remediated'
class RemediationTests(unittest.TestCase):
    def test_archive_replay(self):
        with contextlib.redirect_stdout(io.StringIO()):result=check(ARCHIVE)
        self.assertEqual(sum(row['honest_agents_completed'] for row in result['cases'].values()),4)
    def test_sink_bytes_and_reported_uid_tampering_fail(self):
        with tempfile.TemporaryDirectory(prefix='cstack-r2-remediation-check-',dir=ROOT/'.git') as temporary:
            copy=Path(temporary)/'archive';shutil.copytree(ARCHIVE,copy)
            body=copy/'writable-sink-mount/final/sink/1.body';saved=body.read_bytes();body.write_bytes(saved+b'changed')
            with self.assertRaises(AssertionError):check(copy)
            body.write_bytes(saved)
            runtime=copy/'writable-sink-mount/runtime.json';value=json.loads(runtime.read_text());value['services']['agent-a']['uid']=23700;runtime.write_text(json.dumps(value))
            with self.assertRaises(AssertionError):check(copy)
if __name__=='__main__':unittest.main()
