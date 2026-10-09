"""Linux socket-level, concurrency and retry tests for the scoped journal effect.

No TCP or production effects are exercised. The only checked effect is a
journal append by the trusted reference broker itself.
"""
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
import unittest

from atomic_store import AtomicPolicyJournal, canonical


class SocketCheckedEffectTests(unittest.TestCase):
    def test_parallel_socket_emit_with_policy_updates_and_retries(self):
        if not sys.platform.startswith('linux') or not hasattr(socket,'SO_PEERCRED'):
            self.skipTest('requires Linux SO_PEERCRED')
        with tempfile.TemporaryDirectory(prefix='sc10-socket-effect-') as d:
            directory = Path(d)
            sock = directory/'s.sock'
            journal = directory/'j.jsonl'
            p = subprocess.Popen([sys.executable, str(Path(__file__).with_name('atomic_store.py')),
                                  '--socket',str(sock),'--journal',str(journal),
                                  '--admin-pid',str(os.getpid())],
                                 stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,
                                 stderr=subprocess.PIPE)
            def rpc(req):
                with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
                    s.settimeout(6)
                    s.connect(str(sock))
                    with s.makefile('rwb') as f:
                        f.write(canonical(req)+b'\n')
                        f.flush()
                        response = f.readline()
                        if not response:
                            raise AssertionError('broker closed without a response')
                        return json.loads(response)
            try:
                deadline = time.monotonic()+4
                while not sock.exists() and time.monotonic()<deadline:
                    if p.poll() is not None:
                        self.fail('broker exited before socket ready')
                    time.sleep(.02)
                self.assertTrue(sock.exists())
                self.assertTrue(rpc({'op':'write','policy':{'allow':['a']}})['ok'])
                ops = []
                for i in range(48):
                    if i in (12,36):
                        ops.append({'op':'write','policy':{'allow':[]}})
                    elif i == 24:
                        ops.append({'op':'write','policy':{'allow':['a']}})
                    else:
                        ops.append({'op':'emit','host':'a','payload':str(i),
                                    'request_id': 'id-'+str(i//2)})
                with ThreadPoolExecutor(max_workers=8) as executor:
                    results=list(executor.map(rpc,ops))
                self.assertEqual(len(results),48)
                self.assertTrue(all('ok' in r for r in results),results)
            finally:
                p.terminate()
                try:
                    p.wait(timeout=4)
                except subprocess.TimeoutExpired:
                    p.kill(); p.wait(timeout=4)
                if p.stderr:
                    p.stderr.close()
            s=AtomicPolicyJournal(journal,admin_pid=os.getpid())
            try:
                self.assertTrue(len(s.events)>1)
                seen=set()
                current=[]
                for e in s.events:
                    if e['kind']=='write':
                        current=e['policy']['allow']
                    elif e['kind']=='effect':
                        self.assertIn(e['host'],current)
                        self.assertNotIn(e['request_id'],seen)
                        seen.add(e['request_id'])
                self.assertEqual(len(s.effects),len(seen))
            finally:
                s.close()


if __name__ == '__main__':
    unittest.main()
