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
def release_log_problems(db_path,sink,*,agents=None,approvers=None,reviewers=None):
    """Independent read of the generation r2-v8 release log. Returns None if the database has no release_log (an older
    generation), otherwise the list of problems ([] = consistent). Mirrors the Lean ReleaseLog facts:
    LogSound (the log is the release list: ids, nonces, digests, destinations, agents, leases, costs; costs sum to
    spent), release_event_matches (each row equals the approval it consumed, and its signer/agent/reviewer hold the roles
    when role sets are given), receipt_matches_event (each publication receipt names a logged release, carries that
    event's digest and destination, and equals the SHA-256 of the sink file), one receipt per release. It does not
    prove the sink bytes were written by the receiver, only that they match what was logged."""
    db=sqlite3.connect('file:'+str(Path(db_path).resolve())+'?mode=ro',uri=True)
    try:
        has=lambda name:db.execute("SELECT 1 FROM sqlite_master WHERE name=?",(name,)).fetchone() is not None
        if not has('release_log'):return None
        problems=[]
        spent,=db.execute('SELECT spent FROM meta WHERE id=1').fetchone()
        releases=db.execute('SELECT id,nonce,digest,destination,agent_uid,lease_id,cost FROM releases ORDER BY id').fetchall()
        log=db.execute('SELECT release_id,nonce,digest,destination,agent_uid,lease_id,cost,signer_uid,reviewer_uid FROM release_log ORDER BY release_id').fetchall()
        if [r[:7] for r in log]!=releases:problems.append('release_log differs from releases')
        if sum(r[6] for r in log)!=spent:problems.append('logged costs do not sum to spent')
        if len({r[1] for r in log})!=len(log):problems.append('duplicate nonce in release_log')
        for rid,nonce,digest,dest,agent,lease,cost,signer,reviewer in log:
            ap=db.execute('SELECT digest,destination,agent_uid,lease_id,signer_uid,used FROM approvals WHERE nonce=?',(nonce,)).fetchone()
            if ap is None or ap[:5]!=(digest,dest,agent,lease,signer) or ap[5]!=1:problems.append('release %d differs from its approval'%rid)
            if agents is not None and agent not in agents:problems.append('release %d agent has no agent role'%rid)
            if approvers is not None and signer not in approvers:problems.append('release %d signer has no approver role'%rid)
            if reviewers is not None and reviewer not in reviewers:problems.append('release %d reviewer has no reviewer role'%rid)
            if cost<1:problems.append('release %d has non-positive cost'%rid)
        if has('publication_receipts'):
            logged={r[0]:r for r in log}
            seen=set()
            for rid,observed,dest in db.execute('SELECT release_id,observed_sha256,destination FROM publication_receipts ORDER BY release_id'):
                if rid in seen:problems.append('second receipt for release %d'%rid)
                seen.add(rid)
                if rid not in logged:problems.append('receipt %d has no logged release'%rid);continue
                if (observed,dest)!=(logged[rid][2],logged[rid][3]):problems.append('receipt %d differs from the logged digest or destination'%rid)
                f=Path(sink)/(str(rid)+'.body')
                if not f.is_file() or hashlib.sha256(f.read_bytes()).hexdigest()!=observed:problems.append('receipt %d does not match the sink file'%rid)
        return problems
    finally:db.close()
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--db',required=True);p.add_argument('--sink',required=True);a=p.parse_args();print(json.dumps(reconcile(a.db,a.sink),sort_keys=True))
