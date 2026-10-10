"""Read-only reconciliation: admission is not a durable delivery receipt."""
import argparse
import hashlib
import json
import sqlite3
from pathlib import Path

def reconcile(db_path,sink):
    db=sqlite3.connect('file:'+str(Path(db_path).resolve())+'?mode=ro',uri=True)
    try:
        cap,halted,spent=db.execute('SELECT global_cap,halted,spent FROM meta WHERE id=1').fetchone()
        has_receipts=db.execute("SELECT 1 FROM sqlite_master WHERE name='delivery_receipts'").fetchone()
        receipts=dict(db.execute('SELECT release_id,digest FROM delivery_receipts')) if has_receipts else {}
        rows=[]
        for rid,digest,agent,nonce in db.execute('SELECT id,digest,agent_uid,nonce FROM releases ORDER BY id'):
            p=Path(sink)/(str(rid)+'.body');present=p.exists()
            valid=present and hashlib.sha256(p.read_bytes()).hexdigest()==digest
            receipt=rid in receipts
            status='delivered' if valid and receipt and receipts[rid]==digest else 'unknown-commit' if valid and not receipt else 'admitted' if not present and not receipt else 'inconsistent'
            rows.append({'release_id':rid,'digest':digest,'agent_uid':agent,'nonce':nonce,'file_present':present,'receipt_present':receipt,'classification':status})
        return {'global_cap':cap,'halted':bool(halted),'spent':spent,'admitted':len(rows),'delivered':sum(x['classification']=='delivered' for x in rows),'unknown_commit':sum(x['classification']=='unknown-commit' for x in rows),'records':rows}
    finally:db.close()
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--db',required=True);p.add_argument('--sink',required=True);a=p.parse_args();print(json.dumps(reconcile(a.db,a.sink),sort_keys=True))
