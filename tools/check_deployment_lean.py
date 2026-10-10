#!/usr/bin/env python3
"""Kernel-check raw IR projection and reused contracts at the current source head.
No handwritten acceptance bit and no native_decide. Exit 1 on failed/refuted model.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from security_ir import validate

def projection(ir):
    validate(ir)
    ids={n['id']:i for i,n in enumerate(ir['nodes'])}
    if 'receiver' not in ids or 'broker' not in ids:
        raise ValueError('missing trusted model nodes')
    b=lambda x:'true' if x else 'false'
    # Unknown UID uses sentinel 0, excluded by Accepted; never a claim it was observed.
    nodes=[]
    for n in ir['nodes']:
        if n['type']=='service':
            f=n['facts']; nodes.append('⟨'+','.join([str(ids[n['id']]),str(f['uid'] if f['uid'] is not None else 0),b(f['role']=='agent'),b(f['privileged']),b(f['host_network'])])+'⟩')
    edges=[]
    for e in ir['edges']:
        if e['reachability']=='ABSENT': continue
        authority=e['capability'] in {'write','credential','escape','read','call'} and e['to'] in {'sink','database'}
        edges.append('⟨'+','.join([str(ids[e['from']]),str(ids[e['to']]),b(authority),b(e['reachability']=='UNKNOWN')])+'⟩')
    return '⟨['+','.join(nodes)+'],['+','.join(edges)+'],'+','.join(str(ids[k]) for k in ('receiver','broker','sink','database'))+'⟩'

def check(ir):
    raw=projection(ir)
    build=subprocess.run(['lake','build','ControlStack.Deployment.Contracts'],cwd=ROOT,capture_output=True,text=True)
    if build.returncode: raise ValueError(build.stdout+build.stderr)
    # Projection accepted/refuted is decided IN LEAN, not Python.
    services = [n['facts'] for n in ir['nodes'] if n['type'] == 'service']
    receiver_uid = next(f['uid'] for f in services if f['role'] == 'receiver')
    approvers = [f['uid'] or 0 for f in services if f['role'] == 'approver']
    admins = [f['uid'] or 0 for f in services if f['role'] == 'broker']
    principal = f'roles deployment {receiver_uid or 0} {approvers} {admins}'
    cap = ir['snapshot']['budget']
    source='''import ControlStack.Deployment.Contracts
open ControlStack.Deployment
namespace SliceInstance
def deployment : IR := '''+raw+'''
#eval decide (Accepted deployment)
#print axioms ControlStack.Deployment.protocol_safe
#print axioms ControlStack.Deployment.one_use
#print axioms ControlStack.Deployment.gate_contract
#print axioms ControlStack.Deployment.broker_contract
#print axioms ControlStack.Deployment.runtime_exclusive
#print axioms ControlStack.Deployment.deployment_safe
end SliceInstance
'''
    source += f"\nnamespace SliceInstance\ndef principals : ControlStack.SC26.Roles := {principal}\ntheorem contract_checked (ops : List ControlStack.SC26.Op) (hops : ∀ o ∈ ops, ControlStack.SC26.legal principals o) : ControlStack.SC26.Good principals {cap} (ControlStack.SC26.run principals {cap} ControlStack.SC26.full ControlStack.SC26.init ops) := protocol_safe principals {cap} ops hops\ntheorem one_use_checked (ops : List ControlStack.SC26.Op) : (ControlStack.SC26.run principals {cap} ControlStack.SC26.full ControlStack.SC26.init ops).reserved.Nodup := one_use principals {cap} ops\nend SliceInstance\n#print axioms SliceInstance.contract_checked\n#print axioms SliceInstance.one_use_checked\n"
    with tempfile.TemporaryDirectory(prefix='cstack-lean-') as tmp:
        path=Path(tmp)/'Instance.lean'; path.write_text(source)
        probe=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
        output=probe.stdout+probe.stderr
        if probe.returncode: raise ValueError(output)
        accepted=bool(re.search(r'^true$',output,re.M))
        assertion=('theorem facts_checked : Accepted deployment := by decide' if accepted else 'theorem facts_refuted : ¬ Accepted deployment := by decide')
        source=source.replace('#eval decide (Accepted deployment)',assertion+'\n#print axioms SliceInstance.'+('facts_checked' if accepted else 'facts_refuted'))
        path.write_text(source)
        p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
        output=p.stdout+p.stderr
        groups=re.findall(r'depends on axioms: \[([^\]]*)\]',output)
        count=len(groups)+len(re.findall('does not depend on any axioms',output))
        allowed={'propext','Quot.sound','Classical.choice'}
        if p.returncode or count!=9 or any({x.strip() for x in g.split(',') if x.strip()}-allowed for g in groups) or 'sorryAx' in output:
            raise ValueError(output)
        return {'accepted':accepted,'source':source,'axioms':output}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('ir'); ap.add_argument('--output'); a=ap.parse_args()
    try:
        result=check(json.loads(Path(a.ir).read_text()))
        if a.output: Path(a.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        print(result['axioms']); return 0 if result['accepted'] else 1
    except (OSError,ValueError) as e: print(str(e),file=sys.stderr); return 2
if __name__=='__main__': sys.exit(main())
