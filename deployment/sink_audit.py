"""Sink-side audit independent of reconcile.py: file -> release direction and delegation use.
A file is attributed only if its name is the canonical <release_id>.body AND its bytes hash to that release's digest;
aliased names (leading zeros, non-ASCII digits) are reported as non-body files.
Reads only the saved SQLite backup and the copied sink directory of one finished case.
"""
import hashlib
import re
import sqlite3
from pathlib import Path

CANONICAL=re.compile(r'[1-9][0-9]*\.body')  # ASCII digits, no leading zero: exactly the receiver's str(release_id)+'.body'

def audit(final):
    final=Path(final);db=sqlite3.connect('file:'+str(final/'database.sqlite')+'?mode=ro',uri=True)
    try:
        releases=dict(db.execute('select id,digest from releases'))
        count=lambda table:db.execute('select count(*) from '+table).fetchone()[0]
        delegations,delegated=count('delegations'),count('delegated_releases')
    finally:db.close()
    # .gitkeep is the repository placeholder for an archived empty sink, never a broker output.
    names=sorted(p.name for p in (final/'sink').iterdir() if p.name!='.gitkeep')
    body=[n for n in names if CANONICAL.fullmatch(n)]
    def attributed(name):
        path=final/'sink'/name;release=int(name[:-5])
        return release in releases and path.is_file() and not path.is_symlink() and hashlib.sha256(path.read_bytes()).hexdigest()==releases[release]
    return {'delegations':delegations,'delegated_releases':delegated,
            'non_body_files':[n for n in names if n not in body],
            'unattributed_files':[n for n in body if not attributed(n)]}

def clean(result):return not (result['delegations'] or result['delegated_releases'] or result['non_body_files'] or result['unattributed_files'])
