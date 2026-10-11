"""Sink-side audit independent of reconcile.py: file -> release direction and delegation use.
Reads only the saved SQLite backup and the copied sink directory of one finished case.
"""
import sqlite3
from pathlib import Path

def audit(final):
    final=Path(final);db=sqlite3.connect('file:'+str(final/'database.sqlite')+'?mode=ro',uri=True)
    try:
        releases={row[0] for row in db.execute('select id from releases')}
        count=lambda table:db.execute('select count(*) from '+table).fetchone()[0]
        delegations,delegated=count('delegations'),count('delegated_releases')
    finally:db.close()
    # .gitkeep is the repository placeholder for an archived empty sink, never a broker output.
    names=sorted(p.name for p in (final/'sink').iterdir() if p.name!='.gitkeep')
    body=[n for n in names if n.endswith('.body') and n[:-5].isdecimal()]
    return {'delegations':delegations,'delegated_releases':delegated,
            'non_body_files':[n for n in names if n not in body],
            'unattributed_files':[n for n in body if int(n[:-5]) not in releases]}

def clean(result):return not (result['delegations'] or result['delegated_releases'] or result['non_body_files'] or result['unattributed_files'])
