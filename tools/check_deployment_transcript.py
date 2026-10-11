#!/usr/bin/env python3
"""T4.4 checker: generated module is current, kernel-checked with standard axioms only, and mutated transcripts do NOT check."""
import copy
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.gen_deployment_transcript import OUT,archived,generate

STANDARD={'propext','Quot.sound','Classical.choice'}

def lean(path):
    return subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=900)

def main(negatives=True):
    assert OUT.read_text()==generate(),'stale generated module: run tools/gen_deployment_transcript.py'
    built=subprocess.run(['lake','build','ControlStack.Deployment.TranscriptReplay'],cwd=ROOT,capture_output=True,text=True,timeout=1800)
    assert built.returncode==0,built.stdout+built.stderr
    report=lean(OUT);assert report.returncode==0,report.stdout+report.stderr
    assert 'sorry' not in OUT.read_text().replace('sorryAx','')
    axioms=re.findall(r"depends on axioms: \[(.*?)\]",report.stdout)
    assert axioms and all(set(a.split(', '))<=STANDARD for a in axioms) and 'sorryAx' not in report.stdout,report.stdout
    # Falsifying controls: each mutation is a transcript the model must refuse to certify (the Lean source fails to elaborate).
    rejected=[]
    if negatives:
        events,users=archived()
        def swap_release_caller(e):
            e=copy.deepcopy(e);rel=[x for x in e if x['request']['op']=='effect_release'][0];rel['service']='agent-b';return e
        def accept_replay(e):
            e=copy.deepcopy(e);[x for x in e if x['request']['op']=='effect_release' and not x['response']['ok']][0]['response']['ok']=True;e[8]['response']['result']=0;return e
        def wrong_reviewer(e):
            e=copy.deepcopy(e);[x for x in e if x['request']['op']=='review'][0]['service']='approver';return e
        for label,mutate in (('release by an agent other than the approved one',swap_release_caller),('second release of the same nonce accepted',accept_replay),('review by a non-reviewer UID',wrong_reviewer)):
            with tempfile.TemporaryDirectory(prefix='cstack-transcript-',dir=ROOT/'.git') as tmp:
                path=Path(tmp)/'mutant.lean';path.write_text(generate(mutate(events),users,'Mutant'))
                result=lean(path)
                text=result.stdout+result.stderr
                assert result.returncode!=0 and ('proved that the proposition' in text or 'failed to synthesize' in text),('mutated transcript was certified or failed for an unrelated reason',label,text[:300])
                rejected.append(label)
    print('PASS: transcript module current; standard axioms only ('+str(len(axioms))+' reports);',len(rejected),'mutated transcripts rejected')
if __name__=='__main__':main('--no-negatives' not in sys.argv)
