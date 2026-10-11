#!/usr/bin/env python3
"""T9 trusted-path hardening: each fix from deployment/reviews/trusted-path-code-review-opus.md has a regression test here."""
import contextlib
import io
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
import unittest.mock
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

def wait_listening(path):
    # The socket file appears at bind(), before listen(): wait until a connection is actually accepted.
    for _ in range(200):
        probe=socket.socket(socket.AF_UNIX)
        try:probe.connect(str(path));probe.close();time.sleep(0.3);return  # let the probe connection release its slot
        except OSError:probe.close();time.sleep(0.05)
    raise AssertionError('broker never started listening')

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

    def test_over_a_real_socket_the_gate_decides_and_a_legitimate_delegation_would_succeed(self):
        # A state in which `delegate` is valid: two agents, an active approval owned by the first.
        a1,a2=ME,ME+5;roles=Principals(frozenset({a1,a2}),frozenset({OTHERS[0]}),frozenset({OTHERS[1]}),frozenset({OTHERS[2]}))
        db=self.root/'two.db';c=Controller.bootstrap(db,roles,2)
        digest=c.stage(a1,b'body');c.review(OTHERS[0],digest);expires=int(time.time())+600
        c.issue_lease(OTHERS[2],'lease',a1,2,expires);c.approve(OTHERS[1],'n',digest,'label',a1,'lease',expires)
        request_body={'op':'delegate','nonce':'n','delegate_uid':a2}
        results={}
        for allowed in (False,True):
            sock=self.root/f's{int(allowed)}.sock'
            threading.Thread(target=server.serve,args=(c,sock,allowed),daemon=True).start()
            wait_listening(sock)
            results[allowed]=request(str(sock),request_body)
        self.assertEqual(results[False],{'ok':False,'error':'DENIED'})
        self.assertTrue(results[True]['ok'],'with the gate open the same request succeeds, so the gate is what denied it')
        self.assertEqual(server.delegation_rows(db),1)

    def test_broker_refuses_to_serve_a_database_that_already_holds_delegations(self):
        with contextlib.closing(sqlite3.connect(self.db)) as db:
            db.execute("INSERT INTO delegations (nonce,grantor_uid,delegate_uid) VALUES ('n',?,?)",(ME,OTHERS[0]));db.commit()
        self.assertEqual(server.delegation_rows(self.db),1)
        p=cli(self.root,self.db,'--admins',str(ME))
        self.assertNotEqual(p.returncode,0);self.assertIn('delegation',p.stderr)
        self.assertFalse((self.root/'x.sock').exists())

    def test_scanner_flags_an_entry_that_enables_delegation(self):
        self.assertFalse(delegation_enabled(),'reference entry must not enable delegation')
        head="import os,sys\ncap=1\nos.execv(sys.executable,[sys.executable,'-m','trusted_stack.server','--db','/p',"
        entry=self.root/'entry.py'
        ok=head+"'--bootstrap-cap',str(cap)])\n"
        entry.write_text(ok);self.assertFalse(delegation_enabled(entry),'the conforming shape is accepted')
        for label,source in (('exact flag',head+"'--allow-delegation'])\n"),('abbreviation',head+"'--allow-deleg'])\n"),('short prefix',head+"'--al'])\n"),
                             ('assembled',head+"'--allow'+'-delegation'])\n"),('variable',head+"flag])\n"),('unknown flag',head+"'--other','x'])\n"),
                             ('effect root (a second file-effect path, outside the claim)',head+"'--effect-root','/private/published'])\n"),
                             ('flag as a value',head+"'--socket','--allow-delegation'])\n"),('computed cap',head+"'--bootstrap-cap',cap+1])\n"),
                             ('no execv',"import os\n"),('extra argument',head+"'--bootstrap-cap',str(cap),'x'])\n")):
            with self.subTest(label):
                entry.write_text(source);self.assertTrue(delegation_enabled(entry))

    def test_the_broker_parser_does_not_accept_abbreviated_flags(self):
        p=cli(self.root,self.root/'g.db','--allow')
        self.assertNotEqual(p.returncode,0);self.assertIn('unrecognized',p.stderr);self.assertFalse((self.root/'g.db').exists())

class Serving(Base):
    """T9.3 (review M2, L1, L2, L4, L5, L6): the broker survives hostile input and slow senders."""
    def setUp(self):
        super().setUp()
        self.saved=(server.READ_DEADLINE,server.PER_UID_CONNECTIONS)
        self.addCleanup(lambda:(setattr(server,'READ_DEADLINE',self.saved[0]),setattr(server,'PER_UID_CONNECTIONS',self.saved[1])))
        self.sock=self.root/'b.sock'
    def start(self):
        threading.Thread(target=server.serve,args=(self.controller,self.sock,False),daemon=True).start()
        wait_listening(self.sock)
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

    def test_socket_lock_is_exclusive_and_symlinks_are_refused(self):
        path=self.root/'lock.sock';held=server.lock_socket_path(path)
        with self.assertRaisesRegex(Denied,'another broker'):server.lock_socket_path(path)
        os.close(held);os.close(server.lock_socket_path(path))   # released with the descriptor (a killed broker releases it too)
        link=self.root/'link.sock';(self.root/'elsewhere').write_text('x');(self.root/'link.sock.lock').symlink_to(self.root/'elsewhere')
        with self.assertRaises(OSError):server.lock_socket_path(link)
        loose=self.root/'loose.sock';lock=self.root/'loose.sock.lock';lock.write_text('');lock.chmod(0o644)
        with self.assertRaisesRegex(Denied,'does not own'):server.lock_socket_path(loose)

    def test_two_starts_cannot_both_pass_the_dead_socket_probe(self):
        # Force the interleaving: both starts reach clear_stale_socket together. Without the lock both go on to unlink/bind.
        db=self.root/'pair'/'gate.db';db.parent.mkdir(mode=0o700);controller=Controller.bootstrap(db,principals(),1)
        gate=threading.Barrier(2);real=server.clear_stale_socket;outcome=[]
        def synchronized(path):
            with contextlib.suppress(threading.BrokenBarrierError):gate.wait(1.5)
            return real(path)
        def start():
            try:server.serve(controller,self.root/'pair.sock')
            except Denied as e:outcome.append(str(e))
            except OSError as e:outcome.append('OSError '+str(e))
        with unittest.mock.patch.object(server,'clear_stale_socket',synchronized):
            threads=[threading.Thread(target=start,daemon=True) for _ in range(2)]
            for t in threads:t.start()
            time.sleep(3)
        self.assertEqual(outcome,['another broker is starting or listening on this socket'],outcome)

    def test_simultaneous_broker_starts_leave_exactly_one_listener(self):
        db=self.root/'race'/'gate.db';db.parent.mkdir(mode=0o700);Controller.bootstrap(db,principals(),2)
        argv=[sys.executable,'-m','trusted_stack.server','--db',str(db),'--socket',str(self.root/'x.sock'),'--agents',str(ME+10),'--reviewers',str(ME+11),'--approvers',str(ME+12),'--admins',str(ME)]
        procs=[subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True) for _ in range(6)]
        try:
            wait_listening(self.root/'x.sock');time.sleep(1.5)
            alive=[q for q in procs if q.poll() is None];self.assertEqual(len(alive),1,[q.poll() for q in procs])
            self.assertTrue(all(q.returncode for q in procs if q.poll() is not None))
            self.assertEqual(request(str(self.root/'x.sock'),{'op':'state'})['result']['global_cap'],2)
        finally:
            for q in procs:
                if q.poll() is None:q.terminate()
            for q in procs:q.communicate(timeout=10)

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

    def test_restart_after_a_kill_inside_a_write_transaction(self):
        db=self.root/'hot'/'gate.db';db.parent.mkdir(mode=0o700)
        first=start_cli(self.root,db,2);self.assertIsNone(first.poll());first.send_signal(signal.SIGKILL);first.wait()
        child=("import os,signal,sqlite3\nc=sqlite3.connect(%r,isolation_level=None);c.execute('PRAGMA cache_size=5');c.execute('BEGIN IMMEDIATE');c.execute('UPDATE meta SET spent=spent+1');c.execute('CREATE TABLE junk(x)')\nfor _ in range(400):c.execute('INSERT INTO junk VALUES (zeroblob(4000))')\n"
               "os.kill(os.getpid(),signal.SIGKILL)\n")%str(db)
        subprocess.run([sys.executable,'-c',child]);self.assertTrue(db.with_name('gate.db-journal').exists(),'precondition: a hot journal')
        second=start_cli(self.root,db,2)
        try:
            self.assertIsNone(second.poll(),second.stderr.read() if second.poll() is not None else '')
            self.assertEqual(request(str(self.root/'x.sock'),{'op':'state'})['result']['spent'],0,'the interrupted transaction was rolled back')
        finally:second.send_signal(signal.SIGKILL);second.wait()

    def test_slots_are_reserved_for_trusted_callers_and_the_accept_loop_survives_failures(self):
        active,lock={},threading.Lock()
        for uid in range(1000,1000+server.MAX_CONNECTIONS-server.RESERVED_FOR_TRUSTED):self.assertTrue(server.claim_slot(active,lock,uid))
        self.assertFalse(server.claim_slot(active,lock,5000),'an untrusted caller cannot take a reserved slot')
        for uid in range(2000,2000+server.RESERVED_FOR_TRUSTED):self.assertTrue(server.claim_slot(active,lock,uid,trusted=True))
        self.assertFalse(server.claim_slot(active,lock,3000,trusted=True),'the total is still bounded')
        server.release_slot(active,lock,2000);self.assertTrue(server.claim_slot(active,lock,3000,trusted=True))
        # a failure to start a worker thread drops that connection only
        self.start();original=threading.Thread.start
        calls=[]
        def failing(thread):
            if thread._target is not None and getattr(thread._target,'__name__','')=='worker' and not calls:calls.append(1);raise RuntimeError("can't start new thread")
            return original(thread)
        threading.Thread.start=failing
        try:
            first=raw(self.sock,b'{"op":"state"}\n');first.settimeout(2)
            try:read_reply(first)
            except OSError:pass
            self.state_ok()
        finally:threading.Thread.start=original
        self.assertEqual(calls,[1])

    def test_broker_must_run_as_an_admin_and_not_as_an_agent(self):
        for extra,message in ((('--admins',str(ME+20)),'admin'),(('--agents',str(ME)),'agent')):
            argv_extra=list(extra)
            if '--agents' in argv_extra:
                argv=[sys.executable,'-m','trusted_stack.server','--db',str(self.root/'a.db'),'--socket',str(self.root/'a.sock'),'--agents',str(ME),'--reviewers',str(ME+11),'--approvers',str(ME+12),'--admins',str(ME+13),'--bootstrap-cap','1']
                p=subprocess.run(argv,cwd=ROOT,capture_output=True,text=True,timeout=20)
            else:p=cli(self.root,self.root/'a.db',*extra,cap=1)
            self.assertNotEqual(p.returncode,0);self.assertIn(message,p.stderr)
            self.assertFalse((self.root/'a.db').exists(),'refused before bootstrapping a database')

class HardenedProfile(unittest.TestCase):
    """T9.4 (review M3): the hardened corpus is generated, accepted only when agents cannot regain capabilities."""
    def test_hardened_fixtures_match_their_expectations(self):
        from security_ir.verifier import verify
        from tools.check_deployment_subset_differential import configuration_accepted
        expected=json.loads((ROOT/'examples/compose-two-agent-hardened/expected.json').read_text())
        self.assertGreaterEqual(len(expected),5)
        for name,exp in expected.items():
            with self.subTest(name=name):
                ir=json.loads((ROOT/'security_ir/fixtures-hardened'/(name+'.json')).read_text())
                self.assertEqual(configuration_accepted(ir),exp['lean_accepted'])
                self.assertTrue(exp['bypass'] is None or exp['bypass'] in json.dumps(verify(ir)))

    def test_silence_is_not_hardening(self):
        # T9-M1: an inventory that omits `hardening` must not let an unhardened or undeclared agent through a fresh collection.
        import shutil
        from extractors.compose import collect,sha
        base=ROOT/'examples/compose-two-agent-hardened'
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp);compose=json.loads((base/'clean.compose.json').read_text());runtime=json.loads((base/'clean.runtime.json').read_text())
            for service in runtime['services'].values():service.pop('hardening')
            (tmp/'silent.runtime.json').write_text(json.dumps(runtime))
            for service in compose['services'].values():service.pop('security_opt',None);service.pop('cap_drop',None)
            (tmp/'bare.compose.json').write_text(json.dumps(compose))
            for label,c,r in (('declared but unreported',base/'clean.compose.json',tmp/'silent.runtime.json'),('undeclared and unreported',tmp/'bare.compose.json',tmp/'silent.runtime.json')):
                with self.subTest(label):
                    fresh=collect(c,r,sha(c))
                    self.assertTrue(any('not-established' in e['reason'] for e in fresh['edges']))
                    self.assertFalse(any('not-established' in e['reason'] for e in collect(c,r,sha(c),replay=True)['edges']),'replay of archived v1 inventories keeps its old rules')

    def test_legacy_corpus_is_untouched_and_does_not_require_hardening(self):
        # Archived evidence is bound to these bytes; the hardened profile is additive.
        legacy=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text())
        from tools.check_deployment_subset_differential import configuration_accepted
        self.assertTrue(configuration_accepted(legacy))
        self.assertNotIn('security_opt',(ROOT/'examples/compose-two-agent/clean.compose.json').read_text())

    def test_hardening_is_reported_by_the_collector_and_replay_keeps_v1(self):
        from tools.collect_deployment_docker import inventory_has_hardening,normalize
        compose=json.loads((ROOT/'examples/compose-two-agent-hardened/clean.compose.json').read_text())
        def row(name,security=None,drop=None,add=None):
            return {'Config':{'Labels':{'com.docker.compose.service':name},'User':'23701','Env':['A=1'],'Entrypoint':['/usr/bin/python3','/slice/entry.py'],'Cmd':None},'Image':'sha256:x','Mounts':[],
                    'NetworkSettings':{'Networks':{'p_isolated':{}}},'HostConfig':{'Privileged':False,'CapAdd':add,'CapDrop':drop,'SecurityOpt':security,'Devices':None,'PidMode':'','IpcMode':'private','UsernsMode':'','NetworkMode':'p_isolated','PortBindings':{}}}
        v2=normalize(compose,[row('agent-a',['no-new-privileges:true'],['ALL'])],'p',hardening=True)['agent-a']
        self.assertEqual(v2['hardening'],{'no_new_privileges':True,'cap_drop':['ALL']});self.assertNotIn('unsupported_runtime_security',v2)
        plain=normalize(compose,[row('agent-a')],'p',hardening=True)['agent-a'];self.assertEqual(plain['hardening'],{'no_new_privileges':False,'cap_drop':[]})
        seccomp=normalize(compose,[row('agent-a',['seccomp=unconfined'])],'p',hardening=True)['agent-a'];self.assertIn('unsupported_runtime_security',seccomp)
        self.assertIn('unsupported_runtime_security',normalize(compose,[row('agent-a',None,None,['SYS_ADMIN'])],'p',hardening=True)['agent-a'])
        v1=normalize(compose,[row('agent-a')],'p',hardening=False);self.assertNotIn('hardening',v1['agent-a']);self.assertFalse(inventory_has_hardening(v1));self.assertTrue(inventory_has_hardening({'x':v2}))
        self.assertIn('unsupported_runtime_security',normalize(compose,[row('agent-a',['no-new-privileges:true'])],'p',hardening=False)['agent-a'],'v1 normalization still treats any SecurityOpt as unsupported')

class Availability(Base):
    """Open item 5: HALT latch and staging quota (safety is unchanged: both only refuse more)."""
    def test_halt_latch_blocks_other_work_at_once_and_persists_in_the_background(self):
        class Flaky:
            def __init__(self,inner):self.inner=inner;self.principals=inner.principals;self.calls=0
            def halt(self,uid):
                self.calls+=1
                if self.calls<=3:raise Denied('halt persistence unavailable')
                return self.inner.halt(uid)
            def __getattr__(self,name):return getattr(self.inner,name)
        flaky=Flaky(self.controller);latch=server.HaltLatch();admin=OTHERS[2]
        with self.assertRaises(Denied):server.halt_with_retry(flaky,admin,attempts=2,latch=latch)
        self.assertTrue(latch.requested.is_set());self.assertFalse(latch.persisted.is_set())
        # The database has not recorded the HALT yet, but nothing else may mutate state.
        for req in ({'op':'stage','body_b64':'eA=='},{'op':'review','digest':'0'*64},{'op':'release','nonce':'n','digest':'0'*64,'destination':'d','lease_id':'l'}):
            with self.subTest(op=req['op']),self.assertRaisesRegex(Denied,'HALT requested'):server.run_one(flaky,ME,req,latch=latch)
        self.assertFalse(server.run_one(flaky,ME,{'op':'state'},latch=latch)['halted'])
        for _ in range(100):
            if latch.persisted.wait(0.1):break
        self.assertTrue(latch.persisted.is_set());self.assertTrue(self.controller.state(admin)['halted'])
    def test_halt_that_cannot_even_open_the_database_is_still_retried(self):
        # Review L1: the failure text is 'controller state unavailable' (the database could not be opened), not 'persistence unavailable'.
        class Locked:
            def __init__(self,inner):self.inner=inner;self.principals=inner.principals;self.calls=0
            def halt(self,uid):
                self.calls+=1
                if self.calls<=2:raise Denied('controller state unavailable')
                return self.inner.halt(uid)
        locked=Locked(self.controller);latch=server.HaltLatch()
        with self.assertRaises(Denied):server.halt_with_retry(locked,OTHERS[2],latch=latch)
        for _ in range(100):
            if latch.persisted.wait(0.1):break
        self.assertTrue(latch.persisted.is_set());self.assertTrue(self.controller.state(OTHERS[2])['halted'])
    def test_only_an_admin_can_latch_a_halt(self):
        latch=server.HaltLatch()
        for uid in (ME,OTHERS[0],OTHERS[1],ME+999):
            with self.subTest(uid=uid),self.assertRaises(Denied):server.run_one(self.controller,uid,{'op':'halt'},latch=latch)
            self.assertFalse(latch.requested.is_set())
        self.assertTrue(server.run_one(self.controller,OTHERS[2],{'op':'halt'},latch=latch));self.assertTrue(latch.persisted.is_set())
    def test_staging_quota_refuses_new_bytes_but_not_known_ones(self):
        self.controller.STAGING_QUOTA=10
        digest=self.controller.stage(ME,b'abcdef')
        self.assertEqual(self.controller.stage(ME,b'abcdef'),digest)       # already staged: free
        with self.assertRaisesRegex(Denied,'quota'):self.controller.stage(ME,b'ghijkl')
        self.assertTrue(self.controller.stage(ME,b'wxyz'))                  # exactly at the quota
        with self.assertRaisesRegex(Denied,'quota'):self.controller.stage(ME,b'1')

class ReceiverDebris(Base):
    """T9.5 (review L3): a crash before link leaves .pending-* debris; the receiver reaps it under the DB lock."""
    def setUp(self):
        super().setUp()
        from trusted_stack.outbox_receiver import deliver_record
        self.deliver=deliver_record
        admin=ME;self.agent=admin+10001;self.reviewer=admin+10002;self.approver=admin+10003
        self.roles=Principals(frozenset({self.agent}),frozenset({self.reviewer}),frozenset({self.approver}),frozenset({admin}))
        self.db=self.root/'receiver.db';self.c=Controller.bootstrap(self.db,self.roles,2,lambda:100)
        self.out=self.root/'effects';self.out.mkdir(mode=0o700)
        self.body=b'reviewed\x00local-file-effect';self.digest=self.c.stage(self.agent,self.body)
        self.c.review(self.reviewer,self.digest);self.c.issue_lease(admin,'lease',self.agent,2,200)
        self.c.approve(self.approver,'nonce',self.digest,'label/not-path',self.agent,'lease',150)
        self.release=self.c.release(self.agent,'nonce',self.digest,'label/not-path','lease',record_effect=True)
    def listing(self):return sorted(p.name for p in self.out.iterdir())

    def test_a_real_sigkill_before_link_leaves_debris_that_the_next_delivery_removes(self):
        child=("import os,signal,sys;sys.path.insert(0,%r);from pathlib import Path\n"
               "from trusted_stack.controller import Controller,Principals;from trusted_stack import outbox_receiver as r\n"
               "roles=Principals(frozenset({%d}),frozenset({%d}),frozenset({%d}),frozenset({%d}))\n"
               "os.link=lambda *a,**k:os.kill(os.getpid(),signal.SIGKILL)\n"
               "r.deliver_record(Controller(Path(%r),roles,lambda:100),%d,Path(%r))\n")%(str(ROOT),self.agent,self.reviewer,self.approver,ME,str(self.db),self.release,str(self.out))
        p=subprocess.run([sys.executable,'-c',child],capture_output=True,text=True)
        self.assertEqual(p.returncode,-signal.SIGKILL,p.stderr)
        debris=[n for n in self.listing() if n.startswith('.pending-')];self.assertEqual(len(debris),1,self.listing())
        self.assertNotIn('1.body',self.listing())
        self.assertEqual(self.deliver(self.c,self.release,self.out),'1.body')
        self.assertEqual(self.listing(),['1.body']);self.assertEqual((self.out/'1.body').read_bytes(),self.body)

    def test_only_unlinked_trusted_temporaries_are_reaped(self):
        (self.out/('.pending-'+'a'*32)).write_bytes(self.body[:5])                # truncated prefix, never linked
        (self.out/'notes.txt').write_text('operator file')                        # not the trusted pattern
        (self.out/'.pending-short').write_text('x')                               # wrong pattern
        (self.out/('.pending-'+'b'*32+'0')).write_text('x')                       # wrong pattern (too long)
        (self.out/('.pending-'+'c'*32)).symlink_to(self.root/'elsewhere')         # never followed or removed
        (self.out/('.pending-'+'d'*32)).write_bytes(self.body)
        os.link(self.out/('.pending-'+'d'*32),self.out/'other-name')              # two links: post-link state, not debris
        self.deliver(self.c,self.release,self.out)
        left=self.listing()
        self.assertNotIn('.pending-'+'a'*32,left);self.assertIn('1.body',left)
        for kept in ('notes.txt','.pending-short','.pending-'+'b'*32+'0','.pending-'+'c'*32,'.pending-'+'d'*32,'other-name'):self.assertIn(kept,left)
        self.assertTrue((self.out/('.pending-'+'c'*32)).is_symlink())

    def test_a_halted_system_does_not_touch_the_directory(self):
        debris=self.out/('.pending-'+'e'*32);debris.write_bytes(b'x')
        self.c.halt(ME)
        with self.assertRaises(Denied):self.deliver(self.c,self.release,self.out)
        self.assertTrue(debris.exists())

class ArchivedHardenedRuns(unittest.TestCase):
    """T9.6: live evidence on the hardened profile replays under the independent checkers."""
    def test_five_safe_cases_replay(self):
        from deployment.check_container_run import check
        with contextlib.redirect_stdout(io.StringIO()):result=check(ROOT/'deployment/runs/tier9/containers-hardened')
        self.assertEqual(result['profile'],'hardened');self.assertEqual(set(result['cases']),{'clean','concurrent-cap1','crash-retry','halt-inflight','drift-uid'})
        self.assertFalse({'writable-sink-mount','trusted-role-uid-collision'}&set(result['cases']),'no bypass case is rerun live')
    def test_earlier_generation_archives_still_replay(self):
        # Evidence produced by source generation r2-v3 (before the review fixes) stays checkable through the pin vault.
        from deployment.check_container_run import check as check_run
        from deployment.check_remediated import check as check_demo
        with contextlib.redirect_stdout(io.StringIO()):
            check_run(ROOT/'deployment/runs/tier9/gen-r2-v3/containers-hardened');check_demo(ROOT/'deployment/runs/tier9/gen-r2-v3/demo-dev-clone/remediated')
    def test_demo_remediated_run_replays(self):
        from deployment.check_remediated import check
        with contextlib.redirect_stdout(io.StringIO()):result=check(ROOT/'deployment/runs/tier9/demo-dev-clone/remediated')
        self.assertEqual(set(result['cases']),{'writable-sink-mount','trusted-role-uid-collision'})
    def test_an_unhardened_agent_whose_raw_report_agrees_with_everything_is_still_rejected(self):
        # Rewrite the raw docker inspect, its hash and the derived runtime consistently, so only the hardening
        # assertion (not the raw/derived consistency check) can reject the archive.
        import shutil,hashlib
        from deployment.check_container_run import check
        from tools.collect_deployment_docker import normalize
        with tempfile.TemporaryDirectory(dir=ROOT/'.git') as tmp:
            copy=Path(tmp)/'run';shutil.copytree(ROOT/'deployment/runs/tier9/containers-hardened',copy)
            scan_dir=copy/'clean';raw=scan_dir/'docker-inspect.raw.json';rows=json.loads(raw.read_text())
            for row in rows:
                if row['Config']['Labels']['com.docker.compose.service']=='agent-a':row['HostConfig']['SecurityOpt']=[]
            raw.write_text(json.dumps(rows))
            runtime=json.loads((scan_dir/'runtime.json').read_text());compose=json.loads((scan_dir/'compose.json').read_text())
            runtime['capture']['raw_sha256']=hashlib.sha256(raw.read_bytes()).hexdigest()
            runtime['services']=normalize(compose,rows,'cstack-r2-clean',True);(scan_dir/'runtime.json').write_text(json.dumps(runtime,sort_keys=True,indent=2)+'\n')
            self.assertFalse(runtime['services']['agent-a']['hardening']['no_new_privileges'])
            with self.assertRaises(AssertionError) as caught:check(copy)
            self.assertIn('agent not hardened',str(caught.exception))

if __name__=='__main__':
    unittest.main()
