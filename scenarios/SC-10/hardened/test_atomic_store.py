"""Source-only tests for SC-10 atomic receipt store v2 (no external effects)."""
import json
import os
import socket
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tempfile
import unittest
from atomic_store import AtomicPolicyJournal, canonical


class AtomicStoreTests(unittest.TestCase):
    def test_write_decide_recovery_and_seq(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'log.jsonl'
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertFalse(s.handle(1, {'op':'write', 'policy': {'allow':['a']}})['ok'])
            self.assertEqual(s.handle(9, {'op':'write', 'policy': {'allow':['a']}})['version'],0)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['decision'],'allow')
            self.assertEqual(s.handle(9, {'op':'write', 'policy': {'allow':[]}})['version'],1)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['decision'],'deny')
            s.close()
            s = AtomicPolicyJournal(path, admin_pid=9)
            self.assertEqual(len(s.versions),2)
            self.assertEqual(s.handle(1, {'op':'decide','host':'a'})['version'],1)
            self.assertEqual([e['seq'] for e in s.events], list(range(len(s.events))))
            s.close()

    def test_fail_closed_truncation(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'log'
            path.write_bytes(b'{"seq":0,')
            with self.assertRaises(ValueError):
                AtomicPolicyJournal(path, admin_pid=9)

    def test_fail_closed_altered_past_entry(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'log'
            s=AtomicPolicyJournal(path, admin_pid=9)
            s.handle(9, {'op':'write','policy':{'allow':['a']}})
            s.close()
            raw=path.read_text().replace('"a"','"b"')
            path.write_text(raw)
            with self.assertRaises(ValueError):
                AtomicPolicyJournal(path, admin_pid=9)

    def test_unix_socket_concurrent_requests_are_serialized(self):
        if not sys.platform.startswith("linux") or not hasattr(socket, "SO_PEERCRED"):
            self.skipTest("requires Linux SO_PEERCRED")
        with tempfile.TemporaryDirectory() as d:
            sock = Path(d) / "policy.sock"
            journal = Path(d) / "journal.jsonl"
            process = subprocess.Popen(
                [sys.executable, str(Path(__file__).with_name("atomic_store.py")),
                 "--socket", str(sock), "--journal", str(journal),
                 "--admin-pid", str(os.getpid())],
                stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)

            def rpc(payload):
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as conn:
                    conn.settimeout(8)
                    conn.connect(str(sock))
                    with conn.makefile("rwb") as f:
                        f.write(canonical(payload) + b"\n")
                        f.flush()
                        data = f.readline()
                        self.assertTrue(data, "no reply from serialized store")
                        return json.loads(data)

            try:
                deadline = time.monotonic() + 4
                while not sock.exists() and time.monotonic() < deadline:
                    if process.poll() is not None:
                        self.fail("store exited before binding socket")
                    time.sleep(.03)
                self.assertTrue(sock.exists())
                self.assertTrue(rpc({"op": "write", "policy": {"allow": ["a"]}})["ok"])
                def worker(i):
                    if i % 3 == 0:
                        return rpc({"op": "write", "policy": {"allow": [str(i)]}})
                    return rpc({"op": "decide", "host": str(i)})
                with ThreadPoolExecutor(max_workers=5) as ex:
                    receipts = list(ex.map(worker, range(15)))
                self.assertTrue(all(x.get("ok") for x in receipts), receipts)
            finally:
                process.terminate()
                try:
                    process.wait(timeout=4)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=4)
                if process.stderr:
                    process.stderr.close()
            recovered = AtomicPolicyJournal(journal, admin_pid=os.getpid())
            self.assertEqual(len(recovered.events), 16)
            self.assertEqual([e["seq"] for e in recovered.events], list(range(16)))
            recovered.close()

    def test_unapproved_formats_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            s=AtomicPolicyJournal(Path(d)/'log', admin_pid=9)
            for p in [{'allow':['a','a']}, {'allow':['a'], 'eval':'true'}, {'allow':[123]}, {'allow':'a'}]:
                self.assertFalse(s.handle(9, {'op':'write', 'policy':p})['ok'])
            self.assertFalse(s.handle(1,{'op':'decide','host':'a'})['ok'])
            s.close()


if __name__ == '__main__':
    unittest.main()
