#!/usr/bin/env python3
"""Sealed corpus integrity and static model regression; no live workloads."""
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import tools.check_deployment_heldout as heldout
class HeldoutTests(unittest.TestCase):
    def test_given_hypotheses_and_raw_missing_pins_are_distinct(self):
        seal_before=(heldout.CORPUS/'SEAL.json').read_bytes()
        raw=heldout.evaluate(False,False);model=heldout.evaluate(False,True)
        self.assertEqual(raw['metrics']['unknown_count'],25)
        self.assertEqual(model['metrics']['false_conditional_model_count'],0)
        self.assertEqual(model['metrics']['over_rejection_count'],0)
        self.assertEqual(model['metrics']['plan_model_accepted_count']+model['metrics']['plan_named_residual_count'],25)
        self.assertEqual((heldout.CORPUS/'SEAL.json').read_bytes(),seal_before)
        heldout.sealed_manifest()
    def test_case_byte_changes_break_the_seal(self):
        with tempfile.TemporaryDirectory(prefix='cstack-r2-heldout-seal-',dir=ROOT/'.git') as temporary:
            corpus=Path(temporary)/'corpus';shutil.copytree(heldout.CORPUS,corpus)
            path=corpus/'cases/supported-minimal.compose.json';path.write_bytes(path.read_bytes()+b' ')
            with patch.object(heldout,'CORPUS',corpus):
                with self.assertRaises(AssertionError):heldout.sealed_manifest()
if __name__=='__main__':unittest.main()
