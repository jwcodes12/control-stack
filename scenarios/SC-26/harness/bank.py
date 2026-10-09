#!/usr/bin/env python3
"""The external system ("bank"): the effect of record for SC-26.

Runs as its own UID with a private 0700 state directory. It applies `transfer{key,dest,amount,memo}` only when the
caller's SO_PEERCRED UID is the configured gate UID, and is idempotent by key (SQLite UNIQUE): a repeat with the same
payload answers `duplicate`, a repeat with a different payload answers `conflict`; neither changes the ledger (both
are the model's no-op `bankAppend` on a present key). Every call, applied
or not, goes to an append-only access log, so direct calls by other principals are visible (they become the
model's `bankCall` operations). `ledger`/`access` dumps are allowed only to the auditor UID.
"""
import argparse
import os
import sqlite3
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import Refused, serve, shape, nat  # noqa: E402

SCHEMA = """
CREATE TABLE IF NOT EXISTS ledger(seq INTEGER PRIMARY KEY AUTOINCREMENT, key INTEGER NOT NULL {unique},
  dest INTEGER NOT NULL, amount INTEGER NOT NULL, memo INTEGER NOT NULL, caller INTEGER NOT NULL, t REAL NOT NULL,
  mono INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS access(seq INTEGER PRIMARY KEY AUTOINCREMENT, caller INTEGER NOT NULL, op TEXT NOT NULL,
  key INTEGER, dest INTEGER, amount INTEGER, memo INTEGER, outcome TEXT NOT NULL, t REAL NOT NULL, mono INTEGER);
"""


class Bank:
    def __init__(self, db, gate_uid, auditor_uid, disabled=()):
        self.db, self.gate, self.auditor = db, gate_uid, auditor_uid
        # test-only negative controls; mirrors the Lean `Checks.bankDedup` / `Checks.bankAuth`
        self.dedup, self.auth = "dedup" not in disabled, "auth" not in disabled
        self.local = threading.local()
        c = self.conn()
        c.executescript(SCHEMA.format(unique="UNIQUE" if self.dedup else ""))
        os.chmod(db, 0o600)

    def conn(self):
        c = getattr(self.local, "c", None)
        if c is None:
            c = sqlite3.connect(self.db, isolation_level=None, timeout=30)
            c.execute("PRAGMA journal_mode=WAL")
            c.execute("PRAGMA synchronous=FULL")
            self.local.c = c
        return c

    def test_delay(self, memo):
        """test-only (env SC26_CRASH_HOOK=1): a private file `delay_memo` = "<memo> <seconds>" delays processing of
        transfers with that memo, so a message can be in flight while a HALT commits (attack A10c)"""
        if os.environ.get("SC26_CRASH_HOOK") != "1":
            return
        try:
            mm, sec = (Path(self.db).parent / "delay_memo").read_text().split()
        except (FileNotFoundError, ValueError):
            return
        if int(mm) == memo:
            time.sleep(float(sec))

    def dispatch(self, uid, req):
        op, c = req["op"], self.conn()
        if op == "transfer":
            shape(req, {"key", "dest", "amount", "memo"})
            k, d, a, m = (nat(req[x]) for x in ("key", "dest", "amount", "memo"))
            self.test_delay(m)
            c.execute("BEGIN IMMEDIATE")
            mono = time.monotonic_ns()  # CLOCK_MONOTONIC, shared with the gate on one host; taken under the lock
            try:
                if self.auth and uid != self.gate:
                    outcome = "refused"
                elif self.dedup and (row := c.execute("SELECT dest, amount, memo FROM ledger WHERE key=?",
                                                       (k,)).fetchone()):
                    # same key: idempotent repeat if the payload is identical, otherwise a hard conflict
                    outcome = "duplicate" if tuple(row) == (d, a, m) else "conflict"
                else:
                    c.execute("INSERT INTO ledger(key,dest,amount,memo,caller,t,mono) VALUES(?,?,?,?,?,?,?)",
                              (k, d, a, m, uid, time.time(), mono))
                    outcome = "applied"
                c.execute("INSERT INTO access(caller,op,key,dest,amount,memo,outcome,t,mono) "
                          "VALUES(?,?,?,?,?,?,?,?,?)", (uid, op, k, d, a, m, outcome, time.time(), mono))
                c.execute("COMMIT")
            except BaseException:
                c.execute("ROLLBACK")
                raise
            if outcome == "refused":
                raise Refused("caller is not the gate")
            return outcome
        if op in ("ledger", "access"):
            shape(req, set())
            if uid != self.auditor:
                c.execute("INSERT INTO access(caller,op,outcome,t) VALUES(?,?,?,?)", (uid, op, "refused", time.time()))
                raise Refused("auditor only")
            cols = ("seq,key,dest,amount,memo,caller,t,mono" if op == "ledger"
                    else "seq,caller,op,key,dest,amount,memo,outcome,t,mono")
            rows = c.execute(f"SELECT {cols} FROM {op} ORDER BY seq").fetchall()
            return [dict(zip(cols.split(","), r)) for r in rows]
        raise Refused("unknown op")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--db", required=True)
    p.add_argument("--socket", required=True)
    p.add_argument("--gate-uid", type=int, required=True)
    p.add_argument("--auditor-uid", type=int, required=True)
    p.add_argument("--disable-check", action="append", default=[], choices=["dedup", "auth"],
                   help="TEST-ONLY negative control")
    a = p.parse_args()
    if a.disable_check and os.environ.get("SC26_NEGATIVE_CONTROL") != "1":
        raise SystemExit("--disable-check is a negative control; refusing without SC26_NEGATIVE_CONTROL=1")
    if os.geteuid() in (0, a.gate_uid):
        raise SystemExit("bank must run under its own UID")
    serve(a.socket, Bank(a.db, a.gate_uid, a.auditor_uid, tuple(a.disable_check)).dispatch)


if __name__ == "__main__":
    main()
