#!/usr/bin/env python3
"""Convert archive attribution to a documented Inspect v2 JSON subset; no SDK."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.schema_check import validate

def convert(data):
    validate(data,json.loads((ROOT/'deployment/schemas/episodes-v0.1.json').read_text()))
    prereg=data['prereg'];commits=subprocess.check_output(['git','log','--reverse','--diff-filter=A','--format=%H','--',prereg],cwd=ROOT,text=True).splitlines();assert commits
    created=subprocess.check_output(['git','show','-s','--format=%cI',commits[0]],cwd=ROOT,text=True).strip()
    identity=hashlib.sha256(json.dumps(data,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    samples=[]
    for episode in data['episodes']:
        categories=sorted({o['attribution'] for o in episode['observations'] if o['kind']!='auxiliary_metadata'})
        samples.append({'id':episode['id'],'epoch':1,'input':episode['case'],'target':'Faithful attribution of archived outcomes','messages':[],'scores':{'attribution':{'value':'|'.join(categories),'explanation':'Recorded attribution classes; not a security pass/fail or LLM score.'}},'metadata':episode})
    output={'version':2,'status':'success','eval':{'eval_id':'archive-'+identity[:16],'run_id':identity[:16],'created':created,'task':'deployment-archive-attribution','task_id':data['prereg_sha256'][:16],'task_version':1,'dataset':{'name':'tier2-plus-recorded-honest-remediation','samples':9,'shuffled':False},'model':'scripted/archive','config':{},'tags':['retrospective','scripted','defensive-only'],'metadata':{'scope':data['scope'],'prereg_sha256':data['prereg_sha256'],'created_basis':'First preregistration addition commit time, not episode execution time.','inspect_sdk_validation':'GATED: not installed; no loader pass claimed.','four_arm_eval':'GATED: no cyber-permissive access.','metrics':data['metrics'],'gaps':data['gaps']}},'plan':{'name':'archived-attribution','steps':[]},'stats':{},'samples':samples}
    validate(output,json.loads((ROOT/'deployment/schemas/inspect-export-v2.json').read_text()))
    return output
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('episodes');parser.add_argument('--output',required=True);a=parser.parse_args()
    assert Path(a.output).resolve()!=Path(a.episodes).resolve(),'output must differ from input'
    result=convert(json.loads(Path(a.episodes).read_text()));Path(a.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print('PASS: nine Inspect-shaped v2 samples; no SDK, new episodes or four-arm claim')
