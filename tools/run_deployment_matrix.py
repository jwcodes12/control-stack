#!/usr/bin/env python3
"""Execute scan→verify→report for every fixture and record exact exit codes."""
import argparse
import json
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);ap.add_argument('--lean',action='store_true');ap.add_argument('--boundary-evidence');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
expected=json.loads((ROOT/'examples/compose-two-agent/expected.json').read_text());rows=[]
for name,e in expected.items():
    stem=a.output/name
    steps=[['scan',f'examples/compose-two-agent/{name}.compose.json','--runtime',f'examples/compose-two-agent/{name}.runtime.json','--sha256',e['compose_sha256'],'--output',str(stem)+'.ir.json'],
           ['verify',str(stem)+'.ir.json','--output',str(stem)+'.bundle.json']+(['--lean'] if a.lean else [])+(['--boundary-evidence',a.boundary_evidence] if a.boundary_evidence else []),
           ['report',str(stem)+'.bundle.json','--output',str(stem)+'.md']]
    codes=[]
    for args in steps:
        p=subprocess.run([sys.executable,'tools/cstack.py',*args],cwd=ROOT,capture_output=True,text=True);codes.append(p.returncode)
        want=1 if args[0]=='verify' and (e['verdict']=='UNASSURED' or not a.lean) else 0
        assert p.returncode==want,(name,args,p.stdout,p.stderr)
    b=json.loads(Path(str(stem)+'.bundle.json').read_text()); assert b['verdict']==(e['verdict'] if a.lean else 'UNASSURED')
    if e['bypass']:assert e['bypass'] in json.dumps(b)
    rows.append({'fixture':name,'expected':e['verdict'],'actual':b['verdict'],'exit_codes':codes,'kernel_checked':a.lean,'commands':steps})
    print(name,b['verdict'],codes,flush=True)
(a.output/'matrix.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
