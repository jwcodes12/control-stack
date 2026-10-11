#!/usr/bin/env python3
"""T9 trusted-path hardening: each fix from deployment/reviews/trusted-path-code-review-opus.md has a regression test here."""
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from trusted_stack import server
from trusted_stack.client import request
from trusted_stack.controller import Controller,Denied,Principals
from deployment.scan import delegation_enabled
ME=os.geteuid();OTHERS=(ME+1,ME+2,ME+3)

def principals():return Principals(frozenset({ME}),frozenset({OTHERS[0]}),frozenset({OTHERS[1]}),frozenset({OTHERS[2]}))

class Base(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.root.chmod(0o700)
        self.db=self.root/'gate.db';self.controller=Controller.bootstrap(self.db,principals(),2)

class DelegationProfile(Base):
    """T9.2 (review M1): the reference broker profile has no delegate / revoke_delegation step."""
    def test_disabled_profile_rejects_both_delegation_ops_before_the_controller(self):
        for req in ({'op':'delegate','nonce':'n','delegate_uid':OTHERS[0]},{'op':'revoke_delegation','nonce':'n'}):
            with self.assertRaisesRegex(Denied,'disabled'):server.run_one(self.controller,ME,req,allow_delegation=False)
            with self.assertRaises(Denied) as ctx:server.run_one(self.controller,ME,req,allow_delegation=True)
            self.assertNotIn('disabled',str(ctx.exception),'library default still reaches the controller (delegated-model tests)')
        self.assertEqual(server.delegation_rows(self.db),0)

    def test_a_malformed_delegation_request_stays_a_shape_denial(self):
        with self.assertRaisesRegex(Denied,'unreviewed'):server.run_one(self.controller,ME,{'op':'delegate','extra':1},allow_delegation=False)

    def test_other_operations_are_unchanged(self):
        self.assertIsInstance(server.run_one(self.controller,OTHERS[2],{'op':'state'},allow_delegation=False),dict)

    def test_over_a_real_socket(self):
        sock=self.root/'b.sock';t=threading.Thread(target=server.serve,args=(self.controller,sock,False),daemon=True);t.start()
        for _ in range(100):
            if sock.exists():break
            time.sleep(0.05)
        reply=request(str(sock),{'op':'delegate','nonce':'n','delegate_uid':OTHERS[0]})
        self.assertEqual(reply,{'ok':False,'error':'DENIED'})

    def test_broker_refuses_to_serve_a_database_that_already_holds_delegations(self):
        with sqlite3.connect(self.db) as db:db.execute("INSERT INTO delegations (nonce,grantor_uid,delegate_uid) VALUES ('n',?,?)",(ME,OTHERS[0]))
        self.assertEqual(server.delegation_rows(self.db),1)
        argv=[sys.executable,'-m','trusted_stack.server','--db',str(self.db),'--socket',str(self.root/'x.sock'),'--agents',str(ME),'--reviewers',str(OTHERS[0]),'--approvers',str(OTHERS[1]),'--admins',str(OTHERS[2])]
        # euid is an agent UID here, so use a different agent set to reach the delegation check
        argv[argv.index('--agents')+1]=str(OTHERS[0]+10);argv[argv.index('--reviewers')+1]=str(OTHERS[0]+11)
        p=subprocess.run(argv,cwd=ROOT,capture_output=True,text=True,timeout=20)
        self.assertNotEqual(p.returncode,0);self.assertIn('delegation',p.stderr)
        self.assertFalse((self.root/'x.sock').exists())

    def test_scanner_flags_an_entry_that_enables_delegation(self):
        self.assertFalse(delegation_enabled(),'reference entry must not enable delegation')
        entry=self.root/'entry.py';entry.write_text("import os\nos.execv('x',['x','--agents','1','--allow-delegation'])\n")
        self.assertTrue(delegation_enabled(entry))

if __name__=='__main__':
    unittest.main()
