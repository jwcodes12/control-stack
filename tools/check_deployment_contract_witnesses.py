#!/usr/bin/env python3
"""Kernel check the fixed nonempty contract/witness package; reject missing rows."""
if not __debug__:raise SystemExit('cstack evidence checkers state their checks as assert; refusing to run under python -O')
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
REQUIRED={'Accepted','exclusive_sink','database_custody','runtime_exclusive','agent_not_receiver_uid','agent_call_legal','protocol_safe','one_use','gate_contract','broker_contract','deployment_safe','deployment_broker_safe','accepted_no_avoided_path','accepted_path_safety_monotone','indexed_receipts_sound','path_edge_subset'}
def check():
    package=json.loads((ROOT/'deployment/contract-witnesses.json').read_text());rows=package['contracts']
    expected={'ControlStack.Deployment.'+x for x in REQUIRED}
    assert len(rows)==len(expected) and {r['contract'] for r in rows}==expected
    names=[]
    for row in rows:
        assert row['positive'] and row['negative']
        names.extend([row['contract'],*row['positive'],*row['negative']])
    names=sorted(set(names));assert all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',n) for n in names)
    subprocess.run(['lake','build','ControlStack.Deployment.Witnesses'],cwd=ROOT,check=True,capture_output=True,text=True)
    source='import ControlStack.Deployment.Witnesses\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names)
    with tempfile.TemporaryDirectory(prefix='cstack-r2-witnesses-',dir=ROOT/'.git') as tmp:
        path=Path(tmp)/'WitnessCheck.lean';path.write_text(source)
        p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if p.returncode:raise ValueError(p.stdout+p.stderr)
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",p.stdout)
    assert {name for name,_ in reports}==set(names) and len(reports)==len(names),p.stdout
    for name,axioms in reports:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext','Quot.sound','Classical.choice'},(name,axioms)
    assert 'sorryAx' not in p.stdout
    return {'contracts':len(rows),'declarations':len(names),'axioms':p.stdout,'scope':package['scope']}
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--output');args=a.parse_args();result=check()
    if args.output:Path(args.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('PASS:',result['contracts'],'nonempty contract packages;',result['declarations'],'kernel declarations; standard axioms')
