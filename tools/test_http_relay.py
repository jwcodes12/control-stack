#!/usr/bin/env python3
"""Outbox relay (gate G7): verification before sending, loopback-only destinations, at-least-once with idempotent effect,
append-only acknowledgements. Builds real broker databases with the trusted Controller (generation r2-v8 or later)."""
import contextlib
import hashlib
import os
import sqlite3
import sys
import tempfile
import threading
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import http_relay  # noqa: E402
from tools.http_sink import Sink  # noqa: E402
from trusted_stack.controller import Controller, Principals  # noqa: E402
from trusted_stack.outbox_receiver import deliver_record  # noqa: E402


class RelayCase(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.db, self.out, self.state = base / "gate.db", base / "effects", base / "relay.db"
        self.out.mkdir(mode=0o700)
        admin = os.geteuid()
        self.agent, self.rev, self.appr = admin + 10001, admin + 10002, admin + 10003
        roles = Principals(frozenset({self.agent}), frozenset({self.rev}), frozenset({self.appr}), frozenset({admin}))
        self.now = 100
        self.c = Controller.bootstrap(self.db, roles, 10, lambda: self.now)
        self.admin = admin
        self.c.issue_lease(admin, "lease", self.agent, 10, 1000)
        self.sink = Sink()
        self.server = self.sink.server()
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        self.url = "http://127.0.0.1:%d/ingest" % self.server.server_address[1]

    def release(self, nonce, body, deliver=True):
        digest = self.c.stage(self.agent, body)
        self.c.review(self.rev, digest)
        self.c.approve(self.appr, nonce, digest, "label/x", self.agent, "lease", 500)
        rid = self.c.release(self.agent, nonce, digest, "label/x", "lease", record_effect=True)
        if deliver:
            deliver_record(self.c, rid, self.out)
        return rid, digest

    def run_relay(self, **kw):
        return http_relay.relay(self.db, self.out, self.url, self.state, sleep=lambda s: None, **kw)

    def acks(self):
        with contextlib.closing(sqlite3.connect(self.state)) as con:
            return con.execute("SELECT release_id,digest,status,attempts FROM http_acks ORDER BY release_id").fetchall()


class RelayTests(RelayCase):
    def test_sends_each_verified_release_once_and_a_rerun_sends_nothing(self):
        r1, d1 = self.release("n1", b"alpha")
        r2, d2 = self.release("n2", b"beta")
        report = self.run_relay()
        self.assertEqual((report["verified"], report["sent"], report["failed"]), (2, 2, []))
        self.assertEqual(sorted(self.sink.stored.values()), [b"alpha", b"beta"])
        self.assertEqual(self.acks(), [(r1, d1, 200, 1), (r2, d2, 200, 1)])
        again = self.run_relay()
        self.assertEqual((again["sent"], again["already_acked"]), (0, 2))
        self.assertEqual(len(self.sink.requests), 2)

    def test_a_release_without_a_publication_receipt_is_not_sent(self):
        self.release("n1", b"delivered")
        self.release("n2", b"admitted-only", deliver=False)
        report = self.run_relay()
        self.assertEqual((report["verified"], report["sent"]), (1, 1))
        self.assertEqual(list(self.sink.stored.values()), [b"delivered"])

    def test_a_tampered_sink_file_stops_the_whole_relay_before_any_request(self):
        rid, _ = self.release("n1", b"original")
        path = self.out / ("%d.body" % rid)
        path.chmod(0o600)
        path.write_bytes(b"changed!")
        with self.assertRaisesRegex(http_relay.RelayError, "does not verify"):
            self.run_relay()
        self.assertEqual(self.sink.requests, [])

    def test_lost_acknowledgement_is_retried_and_the_destination_keeps_one_copy(self):
        rid, digest = self.release("n1", b"payload")
        self.sink.faults = ["drop_ack"]  # the bytes were stored, the relay never saw the answer
        report = self.run_relay()
        self.assertEqual((report["sent"], report["failed"]), (1, []))
        self.assertEqual(len(self.sink.requests), 2, "at-least-once: the same bytes were sent twice")
        self.assertEqual(len(self.sink.stored), 1, "the idempotency key kept the effect to one copy")
        self.assertEqual(self.acks(), [(rid, digest, 200, 2)])

    def test_server_error_wrong_echo_and_redirect_are_never_acknowledged(self):
        self.release("n1", b"payload")
        for fault in ("http500", "wrong_echo", "redirect"):
            self.sink.faults = [fault] * 3
            report = self.run_relay()
            self.assertEqual((report["sent"], len(report["failed"])), (0, 1), fault)
            self.assertEqual(self.acks(), [], fault)
        self.assertEqual(self.run_relay()["sent"], 1)  # a healthy destination later succeeds

    def test_acknowledgements_are_append_only(self):
        self.release("n1", b"x")
        self.run_relay()
        with contextlib.closing(sqlite3.connect(self.state)) as con:
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("UPDATE http_acks SET status=500")
            with self.assertRaises(sqlite3.IntegrityError):
                con.execute("DELETE FROM http_acks")

    def test_relay_never_writes_the_broker_database(self):
        self.release("n1", b"x")
        before = hashlib.sha256(self.db.read_bytes()).hexdigest()
        self.run_relay()
        self.assertEqual(hashlib.sha256(self.db.read_bytes()).hexdigest(), before)

    def test_a_database_without_a_release_log_is_refused(self):
        with contextlib.closing(sqlite3.connect(self.db)) as con:
            for name in ("release_log_no_update", "release_log_no_delete"):
                con.execute("DROP TRIGGER " + name)
            con.execute("DROP TABLE release_log")
        with self.assertRaisesRegex(http_relay.RelayError, "no release_log"):
            self.run_relay()


class DestinationTests(unittest.TestCase):
    def test_only_literal_loopback_http_is_accepted_by_default(self):
        for ok in ("http://127.0.0.1:8080/a", "http://127.5.5.5/x", "http://[::1]:9/x"):
            http_relay.check_destination(ok)
        for bad in ("https://127.0.0.1/a", "http://localhost:8080/a", "http://example.com/a", "http://10.0.0.5/a",
                    "http://user:pw@127.0.0.1/a", "ftp://127.0.0.1/a", "http:///a", "http://127.0.0.1/a#frag"):
            with self.assertRaises(http_relay.RelayError, msg=bad):
                http_relay.check_destination(bad)
        http_relay.check_destination("http://localhost:8080/a", allow_hosts={"localhost"})  # explicit operator choice


if __name__ == "__main__":
    unittest.main()
