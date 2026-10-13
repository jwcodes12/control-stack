#!/usr/bin/env python3
"""The archived G3 baseline results (deployment/runs/tier11/baselines) are consistent with the sealed held-out manifests."""
import json
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
RESULTS=ROOT/'deployment/runs/tier11/baselines/results.json'
SAFE='SAFE_IN_SUPPORTED_MODEL'
class BaselineResultTests(unittest.TestCase):
    def setUp(self):self.data=json.loads(RESULTS.read_text())
    def test_rows_match_the_sealed_manifests_and_every_case_was_scanned(self):
        for name,corpus in self.data['corpora'].items():
            manifest=json.loads((ROOT/'deployment/heldout'/name/'manifest.json').read_text())['cases']
            self.assertEqual([r['id'] for r in corpus['rows']],[c['id'] for c in manifest])
            self.assertEqual({r['id']:r['ground_truth'] for r in corpus['rows']},{c['id']:c['ground_truth'] for c in manifest})
            self.assertEqual(corpus['kics_files_scanned'],corpus['cases'],'KICS must have scanned every case')
    def test_summaries_are_recomputed_from_the_rows(self):
        for corpus in self.data['corpora'].values():
            neg=[r for r in corpus['rows'] if r['ground_truth']!=SAFE];safe=[r for r in corpus['rows'] if r['ground_truth']==SAFE]
            for key,row in corpus['summary'].items():
                self.assertEqual(row,{'negatives':len(neg),'caught':sum(r[key]=='REJECT' for r in neg),'safe':len(safe),'over_rejected':sum(r[key]=='REJECT' for r in safe)},key)
    def test_python_baseline_matches_the_archived_numbers_and_inapplicable_tools_are_not_scored(self):
        self.assertEqual(self.data['corpora']['tier6']['summary']['python_rules']['caught'],2)
        self.assertEqual(self.data['corpora']['tier10']['summary']['python_rules']['caught'],0)
        for corpus in self.data['corpora'].values():
            self.assertFalse(corpus['trivy']['applicable']);self.assertFalse(corpus['hadolint']['applicable'])
    def test_the_two_strict_baselines_do_not_discriminate(self):
        for corpus in self.data['corpora'].values():
            for key in ('conftest_owasp','kics_any'):
                s=corpus['summary'][key];self.assertEqual((s['caught'],s['over_rejected']),(s['negatives'],s['safe']))
if __name__=='__main__':unittest.main()
