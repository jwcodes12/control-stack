#!/usr/bin/env python3
"""Regenerate (or --check) deployment/golden: verdict bundles/reports and remediation plans.
Bundles of the frozen legacy corpus never change; the hardened-corpus bundle and the plans follow the current trusted source."""
import argparse
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.plan import build_plan
from extractors.compose import sha
from security_ir.verifier import report,verify
GOLDEN=ROOT/'deployment/golden';HARDENED=ROOT/'examples/compose-two-agent-hardened'

def dumps(value):return json.dumps(value,sort_keys=True,indent=2)+'\n'

def outputs():
    files={}
    for name,directory in (('clean','fixtures'),('writable-sink-mount','fixtures'),('trusted-role-uid-collision','fixtures'),('hardened-clean','fixtures-hardened')):
        bundle=verify(json.loads((ROOT/'security_ir'/directory/(name.removeprefix('hardened-')+'.json')).read_text()))
        files[name+'.bundle.json']=dumps(bundle);files[name+'.report.md']=report(bundle)
    for name in ('writable-sink-mount','trusted-role-uid-collision'):
        compose=HARDENED/(name+'.compose.json')
        plan=build_plan(json.loads(compose.read_text()),json.loads((HARDENED/(name+'.runtime.json')).read_text()),json.loads((ROOT/'security_ir/fixtures-hardened'/(name+'.json')).read_text()),sha(compose))
        files[name+'.plan.json']=dumps(plan)
    return files

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    stale=[]
    for name,text in outputs().items():
        path=GOLDEN/name
        if args.check:
            if not path.exists() or path.read_text()!=text:stale.append(name)
        else:path.write_text(text)
    if stale:raise SystemExit('stale golden output: '+', '.join(stale)+' (run tools/build_deployment_golden.py)')
    print('golden outputs consistent' if args.check else 'golden outputs regenerated')
