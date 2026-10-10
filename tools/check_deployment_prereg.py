#!/usr/bin/env python3
"""Freeze the one explicitly authorized new prereg; preserve all prior guards."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PREREG='prereg/PREREG-DEPLOY-ARMS-v1.md'
FORBIDDEN=re.compile(r'^(ControlStack/EgressGate\.lean|prereg/|gateway/vm/receipts/|data/linuxarena/|data/redwood-leaderboard/|numerics/lastraj_|.*(/evidence/|/receipts/))')
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def check_freeze():
    freeze=json.loads((ROOT/'deployment/prereg-deploy-arms-freeze.json').read_text())
    assert freeze['prereg']==PREREG and freeze['episodes']==9
    path=ROOT/PREREG;assert path.is_file() and not path.is_symlink()
    expected=freeze['prereg_sha256'];assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,'prereg freeze mismatch'
    commits=git('log','--reverse','--diff-filter=A','--format=%H','--',PREREG).decode().splitlines();assert commits,'new prereg has no addition commit'
    first=git('show',commits[0]+':'+PREREG)
    assert hashlib.sha256(first).hexdigest()==expected,'prereg changed after its first addition commit'
    for name,digest in freeze['inputs'].items():
        source=ROOT/name;assert source.resolve().is_relative_to(ROOT) and source.is_file() and not source.is_symlink()
        assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,('frozen attribution input changed',name)
    return freeze

def check_paths(base):
    tokens=git('diff','--no-renames','--name-status','-z',base+'...HEAD').decode().split('\0');tokens=tokens[:-1]
    assert len(tokens)%2==0
    rows=list(zip(tokens[::2],tokens[1::2]));blocked=[]
    for status,name in rows:
        if not FORBIDDEN.search(name):continue
        if name==PREREG and status=='A':check_freeze()
        else:blocked.append((status,name))
    assert not blocked,('immutable proof, evidence or prereg changed',blocked)
    print('PASS: protected paths unchanged; only exact new prereg addition allowed and first-commit hash frozen')
    return rows
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--base');args=parser.parse_args();check_freeze()
    if args.base:check_paths(args.base)
    else:print('PASS: new prereg first-addition hash and nine archived episode inputs frozen')
