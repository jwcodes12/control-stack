#!/usr/bin/env python3
"""Replay real-container artifacts without Docker; reject actual-byte tampering."""
import os
import shutil
import sqlite3
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.check_container_run import check
from deployment.reconcile import release_log_problems
from trusted_stack.controller import Controller, Principals
from trusted_stack.outbox_receiver import deliver_record
ARCHIVE=ROOT/'deployment/runs/tier2/containers-final'
V8=ROOT/'deployment/runs/tier11/containers-hardened'
class R2EvidenceTests(unittest.TestCase):
    def test_independent_reconciliation_and_relocated_archive(self):
        check(ARCHIVE)
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'archive';shutil.copytree(ARCHIVE,copy);check(copy)
            (copy/'crash-retry/after-crash/sink/1.body').write_bytes(b'not approved')
            with self.assertRaises(AssertionError):check(copy)
    def test_nonregular_sink_artifact_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'archive';shutil.copytree(ARCHIVE,copy)
            (copy/'clean/final/sink/extra.body').symlink_to('1.body')
            with self.assertRaises(AssertionError):check(copy)
class ReleaseLogEvidenceTests(unittest.TestCase):
    """Source generation r2-v8 archives carry the persisted release log; the independent checker reads it."""
    def test_archived_r2_v8_run_passes_and_is_relocatable(self):
        check(V8)
        with tempfile.TemporaryDirectory() as tmp:
            copy=Path(tmp)/'run';shutil.copytree(V8,copy);check(copy)
    def test_every_archived_phase_has_a_log_matching_its_releases(self):
        phases=sorted(V8.glob('*/*/database.sqlite'))
        self.assertGreaterEqual(len(phases),6)
        for db in phases:
            self.assertEqual(release_log_problems(db,db.parent/'sink',agents={23701,23702},approvers={23704},reviewers={23703}),[],db)
    def test_the_real_crash_leaves_an_admitted_but_unpublished_release(self):
        after=V8/'crash-retry/after-crash/database.sqlite'
        con=sqlite3.connect('file:%s?mode=ro'%after,uri=True)
        self.assertEqual(con.execute('SELECT COUNT(*) FROM release_log').fetchone(),(1,))
        self.assertFalse(con.execute("SELECT 1 FROM sqlite_master WHERE name='publication_receipts'").fetchone())
        self.assertTrue((after.parent/'sink/1.body').exists())
    def test_rewriting_the_log_or_a_sink_file_or_a_receipt_is_rejected(self):
        for mutate in ('log','sink','receipt'):
            with tempfile.TemporaryDirectory() as tmp:
                copy=Path(tmp)/'run';shutil.copytree(V8,copy)
                db=copy/'clean/final/database.sqlite';os.chmod(db,0o600)
                con=sqlite3.connect(db)
                if mutate=='log':
                    # an attacker who owns the database can drop the append-only triggers; the independent check still notices
                    con.execute('DROP TRIGGER release_log_no_update');con.execute("UPDATE release_log SET digest='%s' WHERE release_id=1"%('0'*64))
                elif mutate=='sink':
                    next((copy/'clean/final/sink').glob('1.body')).write_bytes(b'changed after receipt')
                else:
                    con.execute('DROP TRIGGER publication_receipts_no_update');con.execute("UPDATE publication_receipts SET observed_sha256='%s' WHERE release_id=1"%('1'*64))
                con.commit();con.close()
                with self.assertRaises(AssertionError,msg=mutate):check(copy)
    def test_unit_checker_on_a_fresh_controller_database(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);admin=os.geteuid();a,r,p=admin+10001,admin+10002,admin+10003
            c=Controller.bootstrap(base/'gate.db',Principals(frozenset({a}),frozenset({r}),frozenset({p}),frozenset({admin})),3,lambda:100)
            out=base/'sink';out.mkdir(mode=0o700)
            digest=c.stage(a,b'body');c.review(r,digest);c.issue_lease(admin,'l',a,2,200);c.approve(p,'n',digest,'d/x',a,'l',150)
            rid=c.release(a,'n',digest,'d/x','l',record_effect=True)
            self.assertEqual(release_log_problems(base/'gate.db',out),[])
            deliver_record(c,rid,out)
            self.assertEqual(release_log_problems(base/'gate.db',out,agents={a},approvers={p},reviewers={r}),[])
            self.assertTrue(release_log_problems(base/'gate.db',out,agents={a},approvers={p},reviewers={r+1}))
            (out/('%d.body'%rid)).chmod(0o600);(out/('%d.body'%rid)).write_bytes(b'other')
            self.assertTrue(release_log_problems(base/'gate.db',out))
if __name__=='__main__':unittest.main()
