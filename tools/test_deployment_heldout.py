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
    def test_order_comparison_keeps_ambiguous_targets_and_extra_facts(self):
        from extractors.compose import inventory_order
        repeated={'mounts':[{'source':'/z','target':'/same','read_only':True},{'source':'/a','target':'/same','read_only':False}],'networks':['isolated','isolated'],'env_names':['PYTHONPATH']}
        self.assertEqual(inventory_order(repeated),repeated)
        extra={'mounts':[{'source':'/z','target':'/z','opaque':True},{'source':'/a','target':'/a'}],'networks':['isolated'],'env_names':['SLICE_ROLE','PYTHONPATH']}
        compared=inventory_order(extra)
        self.assertTrue(compared['mounts'][1]['opaque'])
        self.assertEqual(extra['mounts'][0]['source'],'/z')
        self.assertEqual(compared['networks'],['isolated'])

    def test_case_byte_changes_break_the_seal(self):
        with tempfile.TemporaryDirectory(prefix='cstack-r2-heldout-seal-',dir=ROOT/'.git') as temporary:
            corpus=Path(temporary)/'corpus';shutil.copytree(heldout.CORPUS,corpus)
            path=corpus/'cases/supported-minimal.compose.json';path.write_bytes(path.read_bytes()+b' ')
            with patch.object(heldout,'CORPUS',corpus):
                with self.assertRaises(AssertionError):heldout.sealed_manifest()
class RoundTwo(unittest.TestCase):
    """deployment/heldout/tier10: 34 cases sealed by a blind codex exec author for the hardened profile before any scoring."""
    CORPUS=ROOT/'deployment/heldout/tier10'
    def test_seal_and_pre_fix_result_are_preserved(self):
        manifest,seal=heldout.sealed_manifest(self.CORPUS);self.assertEqual((len(manifest['cases']),seal['cases']),(34,34))
        before=json.loads((ROOT/'deployment/runs/tier10/heldout/before-fix-instantiated.json').read_text())
        # The held-out figure: one false CONDITIONAL before the extractor fix; every later figure is contaminated by it.
        self.assertEqual(before['metrics']['false_conditional_model_cases'],['agent-role-impersonation'])
        self.assertEqual(before['corpus_seal_sha256'],heldout.sha(self.CORPUS/'SEAL.json'))
    def test_extractor_now_refuses_the_environment_role_mismatch(self):
        after=heldout.evaluate(False,True,self.CORPUS,True)
        self.assertEqual(after['metrics']['false_conditional_model_count'],0)
        self.assertEqual(after['metrics']['over_rejection_count'],0)
        row=next(r for r in after['rows'] if r['id']=='agent-role-impersonation');self.assertFalse(row['model_accepted'])
        self.assertIn('reference-entry-environment-mismatch',json.dumps(row['obligations']))
        self.assertEqual(after['metrics']['unknown_count'],22)
    def test_environment_rule_applies_to_fresh_rules_only(self):
        import copy
        from extractors.compose import collect,sha
        base=ROOT/'examples/compose-two-agent-hardened'
        c=json.loads((base/'clean.compose.json').read_text());r=json.loads((base/'clean.runtime.json').read_text())
        cases={'agent claims broker':lambda c:c['services']['agent-a']['environment'].update(SLICE_ROLE='broker'),
               'broker does not':lambda c:c['services']['broker']['environment'].update(SLICE_ROLE='agent-a'),
               'python path moved':lambda c:c['services']['receiver']['environment'].update(PYTHONPATH='/tmp/x')}
        with tempfile.TemporaryDirectory(prefix='cstack-r2-env-rule-',dir=ROOT/'.git') as tmp:
            path=Path(tmp)/'c.json';runtime=Path(tmp)/'r.json'
            path.write_text(json.dumps(c));runtime.write_text(json.dumps(r))
            self.assertNotIn('reference-entry-environment-mismatch',json.dumps(collect(path,runtime,sha(path))))
            for label,edit in cases.items():
                with self.subTest(label):
                    changed=copy.deepcopy(c);edit(changed);path.write_text(json.dumps(changed))
                    self.assertIn('reference-entry-environment-mismatch',json.dumps(collect(path,runtime,sha(path))))
                    self.assertNotIn('reference-entry-environment-mismatch',json.dumps(collect(path,runtime,sha(path),replay=True)))
if __name__=='__main__':unittest.main()
