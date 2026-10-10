#!/usr/bin/env python3
"""Kernel regression for every IR fixture; optional on hosts without Lean.
CI deployment-slice/kernel requires Lean and does not skip.
"""
import json
import shutil
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.check_deployment_lean import check
class LeanDeploymentTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('lake'),'Lean unavailable; mandatory kernel job covers this')
    def test_all_fixture_instances_and_standard_axioms(self):
        for path in sorted((ROOT/'security_ir/fixtures').glob('*.json')):
            with self.subTest(fixture=path.stem):
                self.assertEqual(check(json.loads(path.read_text()))['accepted'],path.stem=='clean')
if __name__=='__main__':unittest.main()
