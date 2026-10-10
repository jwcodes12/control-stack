#!/usr/bin/env python3
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.check_deployment_evidence import check
class ArchivedBoundaryTests(unittest.TestCase):
    def test_sink_bytes_and_source_pins(self):
        check(ROOT/'deployment-evidence/runtime-vm/slice-runtime')
if __name__=='__main__':unittest.main()
