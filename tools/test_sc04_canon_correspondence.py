#!/usr/bin/env python3
"""SC-04 runtime/spec correspondence tests for canon.py; not a Lean proof.

The independent specification below represents the narrow runtime boundary:
receiver-visible log records have exactly one template id and two quantised
integer fields. The Python service is tested through its actual Unix sockets,
not by importing its implementation. It is *not* a complete observation or
side-channel certificate: timing, error responses, stdout/stderr, filesystem
side effects, other log producers and deployment bypasses remain assumptions.
"""
import json
import random
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CANON = ROOT / "scenarios" / "SC-04" / "harness" / "canon.py"
EVENTS = ("startup", "request", "db_query", "cache_miss",
          "retry", "timeout", "error", "shutdown")
K, F, Q, FIELD_MAX = 8, 2, 4, 1000


def independent_quant(x):
    try:
        n = int(x)
    except (ValueError, TypeError, OverflowError):
        return 0
    return max(0, min(FIELD_MAX - 1, n)) * Q // FIELD_MAX


def independent_canonical(record):
    event = record.get("event")
    return {
        "template": EVENTS.index(event) if event in EVENTS else 0,
        "fields": [independent_quant(record.get("field" + str(i))) for i in range(F)]
    }


def rpc(path, obj):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as conn:
        conn.settimeout(8)
        conn.connect(str(path))
        stream = conn.makefile("rwb")
        stream.write((json.dumps(obj) + "\n").encode("utf-8"))
        stream.flush()
        line = stream.readline()
        if not line:
            raise RuntimeError("canonicalizer closed socket without reply")
        return json.loads(line)


class Service:
    def __init__(self, directory, free_field=None):
        self.directory = Path(directory)
        args = [sys.executable, "-I", "-S", "-B", str(CANON),
                "--dir", str(self.directory), "--view", str(self.directory / "view.jsonl"),
                "--k", str(K), "--f", str(F), "--q", str(Q),
                "--field-max", str(FIELD_MAX), "--lifetime", "30"]
        if free_field:
            args.extend(("--free-field", free_field))
        self.process = subprocess.Popen(args, stdin=subprocess.DEVNULL,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        text=True)
        line = self.process.stdout.readline()
        if not line.startswith("READY "):
            err = self.process.stderr.read() if self.process.poll() is not None else ""
            self.close()
            raise RuntimeError("service did not start: " + line + " " + err)

    def call(self, role, payload):
        return rpc(self.directory / (role + ".sock"), payload)

    def emit(self, record):
        return self.call("agent", {"op": "emit", "record": record})

    def view(self):
        resp = self.call("receiver", {"op": "view"})
        if resp.get("ok") is not True:
            raise AssertionError(resp)
        return resp["view"]

    def close(self):
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.communicate(timeout=5)
        else:
            self.process.communicate(timeout=5)


class CanonCorrespondence(unittest.TestCase):
    def exercise(self, records, free_field=None):
        with tempfile.TemporaryDirectory(prefix="sc04-spec-") as directory:
            service = Service(directory, free_field=free_field)
            try:
                expected = []
                for record in records:
                    result = service.emit(record)
                    self.assertTrue(result.get("ok"), result)
                    obs = independent_canonical(record)
                    if free_field is not None and free_field in record:
                        obs["free"] = record[free_field]
                    self.assertEqual(result["canonical"], obs)
                    expected.append(obs)
                self.assertEqual(service.view(), expected)
                return expected
            finally:
                service.close()

    def test_edge_cases_and_defaults(self):
        records = [
            {"event": "startup", "field0": -100000, "field1": 999999,
             "note": "hidden token 73715", "message": "attack string"},
            {"event": "error", "field0": None, "field1": "750"},
            {"event": "unexpected", "field0": "not-an-integer", "field1": 249},
            {"field0": 0, "field1": 999, "message": "secret"},
            {"event": "shutdown", "field0": True, "field1": False},
            {"event": "db_query", "field0": 250, "field1": 500},
        ]
        result = self.exercise(records)
        self.assertTrue(all(set(x) == {"template", "fields"} for x in result))
        self.assertEqual(result[0], {"template": 0, "fields": [0, 3]})
        self.assertEqual(result[1], {"template": 6, "fields": [0, 3]})

    def test_deterministic_fuzz_against_independent_spec(self):
        rng = random.Random(413021)
        records = []
        choices = [-1, 0, 1, 249, 250, 499, 500, 750, 998, 999, 1000, 100000,
                   None, "bad", "250", "999"]
        for _ in range(240):
            records.append({
                "event": rng.choice(EVENTS + ("not-allowed",)),
                "field0": rng.choice(choices),
                "field1": rng.choice(choices),
                "free_text": "do not export this" + str(rng.randrange(10**9))
            })
        self.exercise(records)

    def test_roles_and_rejected_invalid_message_do_not_write_view(self):
        with tempfile.TemporaryDirectory(prefix="sc04-spec-") as directory:
            service = Service(directory)
            try:
                self.assertFalse(service.call("receiver", {"op": "emit",
                                 "record": {"event": "error"}})["ok"])
                self.assertFalse(service.call("agent", {"op": "read"})["ok"])
                self.assertEqual(service.view(), [])
                self.assertFalse(service.emit({"event": ["unhashable-list"]})["ok"])
                self.assertEqual(service.view(), [])
            finally:
                service.close()

    def test_negative_control_leaks_explicit_free_field(self):
        source = [{"event": "request", "field0": 1, "field1": 1,
                   "note": "unstructured-secret-738123"}]
        safe = self.exercise(source)
        unsafe = self.exercise(source, free_field="note")
        self.assertNotIn("free", safe[0])
        self.assertEqual(unsafe[0]["free"], source[0]["note"])
        self.assertEqual(set(unsafe[0]), {"template", "fields", "free"})


if __name__ == "__main__":
    unittest.main()
