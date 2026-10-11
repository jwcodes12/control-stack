#!/usr/bin/env python3
import sys
import json
import shutil
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.check_deployment_evidence import check
class ArchivedBoundaryTests(unittest.TestCase):
    def test_sink_bytes_and_source_pins(self):
        check(ROOT/'deployment-evidence/runtime-vm/slice-runtime')
    def test_real_container_sink_and_daemon_inventory(self):
        from tools.check_deployment_container_evidence import check as container_check
        container_check(ROOT/'deployment-evidence/containers')
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'containers';shutil.copytree(ROOT/'deployment-evidence/containers',copy)
            container_check(copy)
            (copy/'clean/sink/1.body').write_bytes(b'unapproved tamper')
            with self.assertRaises(AssertionError):container_check(copy)
    def test_daemon_capture_does_not_drop_security_overrides(self):
        from tools.collect_deployment_docker import normalize
        rows=json.loads((ROOT/'deployment-evidence/containers/clean/docker-inspect.raw.json').read_text())
        c=json.loads((ROOT/'examples/compose-two-agent/clean.compose.json').read_text())
        for field,value in [('GroupAdd',['23700']),('CapAdd',['SYS_ADMIN']),('SecurityOpt',['seccomp=unconfined']),('UsernsMode','host'),('VolumesFrom',['receiver'])]:
            changed=json.loads(json.dumps(rows));changed[0]['HostConfig'][field]=value
            normalized=normalize(c,changed,'sol-pr45-followup')
            self.assertTrue(any('unsupported_runtime_security' in f for f in normalized.values()),field)

if __name__=='__main__':unittest.main()
