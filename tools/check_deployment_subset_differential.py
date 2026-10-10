#!/usr/bin/env python3
"""Disclose, rather than conceal, the documented Python/Lean subset differences.
Kernel-evaluate 200 seeded fixture mutations in one batch. No native_decide.
"""
import argparse
import copy
import json
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.check_deployment_lean import projection
from security_ir.verifier import verify

def run(output=None):
    rng=random.Random(20261010)
    clean=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text());cases=[]
    kinds=['runtime-drift','reviewer-uid-collision','missing-reviewer-role','writable-sink','unknown-edge','privileged','agent-receiver-collision','clean']
    for i in range(200):
        d=copy.deepcopy(clean);kind=kinds[i%len(kinds)]
        services={n['id']:n for n in d['nodes'] if n['type']=='service'}
        agent=rng.choice(['agent-a','agent-b']);f=services[agent]['facts']
        if kind=='runtime-drift': f['runtime_match']=rng.choice(['MISSING','DRIFT'])
        elif kind=='reviewer-uid-collision': f['uid']=services['reviewer']['facts']['uid']
        elif kind=='missing-reviewer-role':services['reviewer']['facts']['role']='approver'
        elif kind in {'writable-sink','unknown-edge'}:
            e=copy.deepcopy(d['edges'][0]);e.update({'from':agent,'to':'sink','capability':'write','reachability':'UNKNOWN' if kind=='unknown-edge' else 'PRESENT','authorization':rng.choice(['FORBIDDEN','PERMITTED','UNKNOWN']),'reason':'seeded mutation'})
            if kind=='unknown-edge':e['provenance']['kind']='UNKNOWN'
            d['edges'].append(e)
        elif kind=='privileged':f['privileged']=True
        elif kind=='agent-receiver-collision':f['uid']=services['receiver']['facts']['uid']
        python_ok=not any(o['status'] in {'REFUTED','UNASSESSED'} and o['premise']!='Lean-contract-instances' for o in verify(d)['obligations'])
        cases.append((kind,d,python_ok))
    subprocess.run(['lake','build','ControlStack.Deployment.Contracts'],cwd=ROOT,check=True,capture_output=True)
    source='import ControlStack.Deployment.Contracts\nopen ControlStack.Deployment\nset_option maxRecDepth 8192\nset_option maxHeartbeats 20000000\n#eval IO.println (String.intercalate "," ((['+','.join(projection(d) for _,d,_ in cases)+'] : List IR).map (fun d => toString (decide (Accepted d)))))\n'
    with tempfile.TemporaryDirectory(prefix='cstack-subset-') as tmp:
        p=Path(tmp)/'Subset.lean';p.write_text(source)
        proc=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    if proc.returncode:raise ValueError(proc.stdout+proc.stderr)
    values=proc.stdout.strip().split(',')
    assert set(values)<={'true','false'},proc.stdout
    kernel=[v=='true' for v in values]
    assert len(kernel)==200
    proofs='import ControlStack.Deployment.Contracts\nopen ControlStack.Deployment\nset_option maxRecDepth 8192\nset_option maxHeartbeats 20000000\n'
    for i,((_,d,_),accepted) in enumerate(zip(cases,kernel)):
        proposition=('Accepted' if accepted else '¬ Accepted')+' ('+projection(d)+')'
        proofs+=f'theorem mutation_{i} : {proposition} := by decide\n#print axioms mutation_{i}\n'
    with tempfile.TemporaryDirectory(prefix='cstack-subset-proofs-') as tmp:
        path=Path(tmp)/'Proofs.lean';path.write_text(proofs)
        proved=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if proved.returncode:raise ValueError(proved.stdout+proved.stderr)
    groups=re.findall(r'depends on axioms: \[([^\]]*)\]',proved.stdout)
    count=len(groups)+len(re.findall('does not depend on any axioms',proved.stdout))
    assert count==200 and 'sorryAx' not in proved.stdout
    assert all({x.strip() for x in g.split(',') if x.strip()}<={'propext','Quot.sound','Classical.choice'} for g in groups)

    rows=[]
    for i,((kind,d,python_ok),lean_ok) in enumerate(zip(cases,kernel)):
        mismatch=kind in {'runtime-drift','reviewer-uid-collision','missing-reviewer-role'}
        assert (python_ok!=lean_ok)==mismatch,(kind,python_ok,lean_ok)
        assert not python_ok or lean_ok,('Python accepted/kernel refuted',kind)
        rows.append({'mutation':i,'kind':kind,'python_configuration_accepted':python_ok,'lean_subset_accepted':lean_ok,'expected_disclosed_difference':mismatch})
    result={'seed':20261010,'mutations':200,'kernel_checked_mutations':200,'agreement':125,'documented_subset_differences':75,'python_accepts_kernel_refutes':0,'rows':rows,'scope':'fallback: strict subset documented; mismatch intentionally makes final verdict UNASSURED through Python obligations'}
    if output:Path(output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('PASS: 200 seeded mutations; 125 agreements, 75 disclosed subset differences, no Python acceptance with kernel refutation')
    return result
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output');a=ap.parse_args();run(a.output)
