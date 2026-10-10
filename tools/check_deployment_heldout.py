#!/usr/bin/env python3
"""Frozen static reference-profile corpus; no live launch or runtime assurance."""
import argparse
import hashlib
import json
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from extractors.compose import collect,sha
from security_ir.verifier import verify
from tools.check_deployment_subset_differential import configuration_accepted
from deployment.plan import build_plan,apply_patch
from tools.test_deployment_plan import proposed_inventory
from deployment.rules_baseline import assess
CORPUS=ROOT/'deployment/heldout/tier6'

def sealed_manifest():
    seal=json.loads((CORPUS/'SEAL.json').read_text())
    for name,digest in seal['files'].items():
        path=CORPUS/name;assert path.resolve().is_relative_to(CORPUS.resolve()) and path.is_file() and not path.is_symlink()
        assert sha(path)==digest,('sealed corpus changed',name)
    manifest=json.loads((CORPUS/'manifest.json').read_text());assert len(manifest['cases'])==seal['cases']==25
    return manifest,seal

def evaluate(kernel=True):
    manifest,seal=sealed_manifest();rows=[];irs=[];proposed_irs=[]
    with tempfile.TemporaryDirectory(prefix='cstack-r2-heldout-',dir=ROOT/'.git') as temporary:
        cp=Path(temporary)/'compose.json';rp=Path(temporary)/'runtime.json'
        for case in manifest['cases']:
            paths=[CORPUS/case[key] for key in ('compose','runtime')]
            assert all(p.resolve().is_relative_to(CORPUS.resolve()) for p in paths)
            c,r=[json.loads(p.read_text()) for p in paths];ir=collect(*paths,sha(paths[0]))
            # Authored selected facts are hypotheses, never daemon observations.
            for p in ir['sources']+[item['provenance'] for item in ir['nodes']+ir['edges']]:
                if p['sha256']==sha(paths[1]):p['kind']='DECLARED'
            accepted=configuration_accepted(ir);obligations=[o for o in verify(ir)['obligations'] if o['premise']!='Lean-contract-instances' and o['status'] in {'REFUTED','UNASSESSED'}]
            model_verdict='MODEL_ACCEPTED' if accepted else 'UNKNOWN' if any(o['status']=='UNASSESSED' for o in obligations) else 'REFUTED'
            plan=build_plan(c,r,ir,sha(paths[0]));candidate=apply_patch(c,plan['patch']);inventory=proposed_inventory(candidate,c,r)
            cp.write_text(json.dumps(candidate));rp.write_text(json.dumps(inventory));proposed=collect(cp,rp,sha(cp))
            for p in proposed['sources']+[item['provenance'] for item in proposed['nodes']+proposed['edges']]:
                if p['sha256']==sha(rp):p['kind']='DECLARED'
            plan_accepted=configuration_accepted(proposed);remaining=[o for o in verify(proposed)['obligations'] if o['premise']!='Lean-contract-instances' and o['status'] in {'REFUTED','UNASSESSED'}]
            rows.append({'id':case['id'],'ground_truth':case['ground_truth'],'author_reason':case['reason'],'model_verdict':model_verdict,'model_accepted':accepted,'obligations':obligations,'plan_ops':len(plan['patch']),'plan_model_accepted':plan_accepted,'plan_remaining':remaining,'plan_residuals':plan['residuals'],'baseline':assess(c)})
            irs.append(ir);proposed_irs.append(proposed)
    axioms=None
    if kernel:
        from deployment.kernel import check_many
        values,axioms=check_many(irs+proposed_irs)
        assert values==[r['model_accepted'] for r in rows]+[r['plan_model_accepted'] for r in rows]
    safe=[r for r in rows if r['ground_truth']=='SAFE_IN_SUPPORTED_MODEL'];negative=[r for r in rows if r not in safe]
    false=[r['id'] for r in negative if r['model_accepted']];over=[r['id'] for r in safe if not r['model_accepted']]
    metrics={'cases':len(rows),'supported_cases':len(safe),'negative_cases':len(negative),'false_conditional_model_count':len(false),'false_conditional_model_cases':false,'over_rejection_count':len(over),'over_rejection_rate':len(over)/len(safe),'unknown_count':sum(r['model_verdict']=='UNKNOWN' for r in rows),'unknown_rate':sum(r['model_verdict']=='UNKNOWN' for r in rows)/len(rows),'plan_model_accepted_count':sum(r['plan_model_accepted'] for r in rows),'plan_named_residual_count':sum(not r['plan_model_accepted'] and bool(r['plan_residuals']) for r in rows),'baseline_negative_caught':sum(r['baseline']['verdict']=='REJECT' for r in negative),'baseline_negative_missed':sum(r['baseline']['verdict']=='ALLOW' for r in negative),'baseline_supported_rejected':sum(r['baseline']['verdict']=='REJECT' for r in safe)}
    return {'evaluator_sha256':sha(Path(__file__)),'baseline_sha256':sha(ROOT/'deployment/rules_baseline.py'),'basis':'Static finite reference-profile extraction and planner evaluation under author-given image, custody and selected-inventory hypotheses. MODEL_ACCEPTED is not a live CONDITIONAL verdict. Fresh image/realpath observation and Compose CLI normalization are covered separately by Tier 3, not this corpus. No runtime launch.','corpus_seal_sha256':sha(CORPUS/'SEAL.json'),'author_seal_sha256':seal['author_seal_sha256'],'kernel_certificates':len(irs+proposed_irs) if kernel else 0,'axioms':axioms,'metrics':metrics,'rows':rows,'gated_baseline':'Actual OPA/Conftest unavailable; this baseline is hand-written Python.'}
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);parser.add_argument('--no-kernel',action='store_true');a=parser.parse_args();result=evaluate(not a.no_kernel);Path(a.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result['metrics'],sort_keys=True));assert result['metrics']['false_conditional_model_count']==0,'stop-the-line false model assurance';assert result['metrics']['plan_model_accepted_count']+result['metrics']['plan_named_residual_count']==25
