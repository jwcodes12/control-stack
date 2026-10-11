#!/usr/bin/env python3
"""T9 trusted-path hardening: each fix from deployment/reviews/trusted-path-code-review-opus.md has a regression test here."""
import contextlib
import json
import os
import signal
import socket
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

def cli(root,db,*extra,cap=None,timeout=20):
    argv=[sys.executable,'-m','trusted_stack.server','--db',str(db),'--socket',str(root/'x.sock'),'--agents',str(ME+10),'--reviewers',str(ME+11),'--approvers',str(ME+12),*extra]
    if '--admins' not in extra:argv+=['--admins',str(ME)]
    if cap is not None:argv+=['--bootstrap-cap',str(cap)]
    return subprocess.run(argv,cwd=ROOT,capture_output=True,text=True,timeout=timeout)

def start_cli(root,db,cap):
    argv=[sys.executable,'-m','trusted_stack.server','--db',str(db),'--socket',str(root/'x.sock'),'--agents',str(ME+10),'--reviewers',str(ME+11),'--approvers',str(ME+12),'--admins',str(ME),'--bootstrap-cap',str(cap)]
    proc=subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)
    for _ in range(100):
        if proc.poll() is not None:break
        try:
            probe=socket.socket(socket.AF_UNIX);probe.connect(str(root/'x.sock'));probe.close();break
        except OSError:probe.close();time.sleep(0.05)
    return proc

def raw(path,data=b'',keep=False):
    s=socket.socket(socket.AF_UNIX);s.settimeout(5);s.connect(str(path))
    try:
        if data:s.sendall(data)
    except (BrokenPipeError,ConnectionResetError):pass   # the broker may refuse and close before the whole frame is sent
    return s

def read_reply(s):
    out=bytearray()
    while not out.endswith(b'\n'):
        part=s.recv(4096)
        if not part:break
        out.extend(part)
    return json.loads(out) if out else None

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
        with contextlib.closing(sqlite3.connect(self.db)) as db:
            db.execute("INSERT INTO delegations (nonce,grantor_uid,delegate_uid) VALUES ('n',?,?)",(ME,OTHERS[0]));db.commit()
        self.assertEqual(server.delegation_rows(self.db),1)
        p=cli(self.root,self.db,'--admins',str(ME))
        self.assertNotEqual(p.returncode,0);self.assertIn('delegation',p.stderr)
        self.assertFalse((self.root/'x.sock').exists())

    def test_scanner_flags_an_entry_that_enables_delegation(self):
        self.assertFalse(delegation_enabled(),'reference entry must not enable delegation')
        entry=self.root/'entry.py';entry.write_text("import os\nos.execv('x',['x','--agents','1','--allow-delegation'])\n")
        self.assertTrue(delegation_enabled(entry))

class Serving(Base):
    """T9.3 (review M2, L1, L2, L4, L5, L6): the broker survives hostile input and slow senders."""
    def setUp(self):
        super().setUp()
        self.saved=(server.READ_DEADLINE,server.PER_UID_CONNECTIONS)
        self.addCleanup(lambda:(setattr(server,'READ_DEADLINE',self.saved[0]),setattr(server,'PER_UID_CONNECTIONS',self.saved[1])))
        self.sock=self.root/'b.sock'
    def start(self):
        threading.Thread(target=server.serve,args=(self.controller,self.sock,False),daemon=True).start()
        for _ in range(100):
            if self.sock.exists():break
            time.sleep(0.05)
    def state_ok(self):
        reply=request(str(self.sock),{'op':'state'});self.assertTrue(reply['ok']);return reply

    def test_deeply_nested_json_is_denied_and_the_broker_keeps_serving(self):
        self.start()
        for frame in (b'{"a":'*100000+b'1'+b'}'*100000+b'\n',b'['*200000+b']'*200000+b'\n'):
            s=raw(self.sock,frame);self.assertEqual(read_reply(s),{'ok':False,'error':'DENIED'});s.close()
        self.state_ok()

    def test_slow_sender_neither_blocks_other_callers_nor_outlives_the_deadline(self):
        server.READ_DEADLINE=0.6;self.start()
        slow=raw(self.sock,b'{');started=time.monotonic()
        t0=time.monotonic();self.state_ok();self.assertLess(time.monotonic()-t0,1.0,'a trickling sender stalled another caller')
        slow.sendall(b' ');time.sleep(0.3);slow.sendall(b' ')   # keeps trickling, never finishes
        self.assertEqual(read_reply(slow),{'ok':False,'error':'DENIED'})
        self.assertLess(time.monotonic()-started,2.0,'deadline covers the whole frame, not each read')
        self.state_ok()

    def test_a_frame_that_does_not_start_an_object_is_refused_at_the_first_byte(self):
        server.READ_DEADLINE=30;self.start()
        s=raw(self.sock,b'x');t0=time.monotonic()
        self.assertEqual(read_reply(s),{'ok':False,'error':'DENIED'});self.assertLess(time.monotonic()-t0,1.0)

    def test_one_uid_cannot_hold_every_slot(self):
        server.READ_DEADLINE=5;server.PER_UID_CONNECTIONS=1;self.start()
        hold=raw(self.sock,b'{');time.sleep(0.2)
        t0=time.monotonic();extra=raw(self.sock,b'{"op":"state"}\n')
        self.assertEqual(read_reply(extra),{'ok':False,'error':'DENIED'});self.assertLess(time.monotonic()-t0,1.0)
        hold.close();time.sleep(0.3);self.state_ok()

    def test_halt_is_retried_until_it_commits_and_other_denials_are_final(self):
        class Fake:
            def __init__(self,failures,message):self.calls=0;self.failures=failures;self.message=message
            def halt(self,uid):
                self.calls+=1
                if self.calls<=self.failures:raise Denied(self.message)
                return True
        busy=Fake(2,'halt persistence unavailable');self.assertTrue(server.halt_with_retry(busy,1));self.assertEqual(busy.calls,3)
        role=Fake(1,'OS principal not authorized for role')
        with self.assertRaises(Denied):server.halt_with_retry(role,1)
        self.assertEqual(role.calls,1)
        never=Fake(99,'halt persistence unavailable')
        with self.assertRaises(Denied):server.halt_with_retry(never,1,attempts=3)
        self.assertEqual(never.calls,3)

    def test_stale_socket_is_cleared_but_live_sockets_and_files_are_not(self):
        stale=self.root/'stale.sock';dead=socket.socket(socket.AF_UNIX);dead.bind(str(stale));dead.close()
        self.assertTrue(stale.exists());server.clear_stale_socket(stale);self.assertFalse(stale.exists())
        live=self.root/'live.sock';listener=socket.socket(socket.AF_UNIX);listener.bind(str(live));listener.listen(1);self.addCleanup(listener.close)
        with self.assertRaisesRegex(Denied,'already listening'):server.clear_stale_socket(live)
        plain=self.root/'plain';plain.write_text('x')
        with self.assertRaisesRegex(Denied,'refusing'):server.clear_stale_socket(plain)

    def test_restart_after_a_kill_reuses_the_database_and_checks_the_cap(self):
        db=self.root/'restart'/'gate.db';db.parent.mkdir(mode=0o700)
        first=start_cli(self.root,db,2)
        try:
            self.assertIsNone(first.poll(),first.stderr.read() if first.poll() is not None else '')
            self.assertEqual(request(str(self.root/'x.sock'),{'op':'state'})['result']['global_cap'],2)
        finally:first.send_signal(signal.SIGKILL);first.wait()
        self.assertTrue((self.root/'x.sock').exists(),'a killed broker leaves its socket behind')
        second=start_cli(self.root,db,2)
        try:
            self.assertIsNone(second.poll(),second.stderr.read() if second.poll() is not None else '')
            self.assertEqual(request(str(self.root/'x.sock'),{'op':'state'})['result']['global_cap'],2)
        finally:second.send_signal(signal.SIGKILL);second.wait()
        wrong=cli(self.root,db,cap=5);self.assertNotEqual(wrong.returncode,0);self.assertIn('disagrees',wrong.stderr)

    def test_broker_must_run_as_an_admin_and_not_as_an_agent(self):
        for extra,message in ((('--admins',str(ME+20)),'admin'),(('--agents',str(ME)),'agent')):
            argv_extra=list(extra)
            if '--agents' in argv_extra:
                argv=[sys.executable,'-m','trusted_stack.server','--db',str(self.root/'a.db'),'--socket',str(self.root/'a.sock'),'--agents',str(ME),'--reviewers',str(ME+11),'--approvers',str(ME+12),'--admins',str(ME+13),'--bootstrap-cap','1']
                p=subprocess.run(argv,cwd=ROOT,capture_output=True,text=True,timeout=20)
            else:p=cli(self.root,self.root/'a.db',*extra,cap=1)
            self.assertNotEqual(p.returncode,0);self.assertIn(message,p.stderr)
            self.assertFalse((self.root/'a.db').exists(),'refused before bootstrapping a database')

if __name__=='__main__':
    unittest.main()
