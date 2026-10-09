#!/usr/bin/env python3
"""The SC-26 transaction gate: a runtime implementation of the Lean model `ControlStack.SC26.step` with checks `full`.

Runs as its own UID (the model's `R.gate`, the only credential the bank accepts), with a private 0700 SQLite state.
The caller of every operation is its SO_PEERCRED UID; identity fields in requests are refused (exact shapes).

Trace = linearization. Each model operation is decided and recorded (`trace` table) inside ONE `BEGIN IMMEDIATE`
transaction together with its state change, so the trace order is the commit order and a crash can never leave a
state change without its trace row or vice versa. Mapping to model operations:

  request{tx}      -> Op.request caller tx       (the assigned id equals the model's `next`)
  approve{id,tx}   -> Op.approve caller id tx
  execute{id}      -> Op.execute caller id        (reservation + spend), then an internal deliver
  deliver{id}      -> Op.deliver id               (any caller may poke a retry; the gate's own deliveries too)
  halt{}           -> Op.halt caller

A `deliver` trace row is the model's `deliver` (the gate SENDS: the message joins `net`). It is committed after the
halt check and BEFORE the bank is contacted, under `dlock`, which `halt` also takes, so no send can be logged after
a halt. Each time the bank processes the message is the model's `arrive` (the bank's access log, not this trace).
Recovery at startup, unless halted, re-sends every unacknowledged message and issues a new deliver for every
reservation that was never sent. After a halt the gate makes NO bank call at all: intents committed but not sent
stay stranded (unpaid, listed by `dump`); only messages already transmitted may still land (the model's `arrive`).
Refused operations are recorded with accepted=0 (model: identity step). Malformed requests are recorded as
`malformed` and are not model operations.

Test-only fault injection: with env SC26_CRASH_HOOK=1, if the private file `crash_at` contains `after_reserve`,
`after_intent_before_send` or `after_bank_ack`, the gate deletes it and exits with status 137 at that point; if
the private file `hold_recovery` exists at start, the gate serves first and runs recovery only after it is deleted
(so the harness can HALT a restarted gate before recovery). A bank
answer `conflict` (same key, different payload) is a hard error: recorded, never marked delivered.
"""
import argparse
import json
import os
import sqlite3
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import Refused, make_server, shape, nat, tx_of  # noqa: E402
from client import call  # noqa: E402

SCHEMA = """
CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS requests(id INTEGER PRIMARY KEY, requester INTEGER NOT NULL,
  dest INTEGER NOT NULL, amount INTEGER NOT NULL, memo INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS approvals(seq INTEGER PRIMARY KEY AUTOINCREMENT, id INTEGER NOT NULL,
  approver INTEGER NOT NULL, dest INTEGER NOT NULL, amount INTEGER NOT NULL, memo INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS reserved(id INTEGER PRIMARY KEY, seq INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS delivery(seq INTEGER PRIMARY KEY AUTOINCREMENT, id INTEGER NOT NULL,
  acked INTEGER NOT NULL DEFAULT 0, outcome TEXT);
CREATE TABLE IF NOT EXISTS trace(seq INTEGER PRIMARY KEY AUTOINCREMENT, op TEXT NOT NULL, caller INTEGER NOT NULL,
  args TEXT NOT NULL, accepted INTEGER NOT NULL, result TEXT, t REAL NOT NULL);
"""


class Gate:
    def __init__(self, state_dir, cap, agents, approvers, admins, auditor, bank_socket, disabled=()):
        self.dir = Path(state_dir)
        self.db = str(self.dir / "gate.sqlite3")
        self.agents, self.approvers, self.admins = frozenset(agents), frozenset(approvers), frozenset(admins)
        self.auditor, self.bank_socket = auditor, bank_socket
        # test-only negative controls; mirrors the Lean `Checks` flags handled by the gate
        self.on = {k: k not in disabled for k in ("distinct", "payload", "nonce", "cap", "halt")}
        self.uid = os.geteuid()
        self.local = threading.local()
        self.dlock = threading.Lock()
        self.recovered = False
        c = self.conn()
        c.executescript(SCHEMA)
        os.chmod(self.db, 0o600)
        c.execute("BEGIN IMMEDIATE")
        have = dict(c.execute("SELECT k, v FROM meta").fetchall())
        if not have:
            c.executemany("INSERT INTO meta VALUES(?,?)", [("next", 0), ("spent", 0), ("halted", 0), ("cap", cap)])
        elif have["cap"] != cap:
            c.execute("ROLLBACK")
            raise SystemExit("cap differs from the initialized state; refusing to start")
        c.execute("COMMIT")

    # ---- plumbing ----
    def conn(self):
        c = getattr(self.local, "c", None)
        if c is None:
            c = sqlite3.connect(self.db, isolation_level=None, timeout=60)
            c.execute("PRAGMA journal_mode=WAL")
            c.execute("PRAGMA synchronous=FULL")
            self.local.c = c
        return c

    def hook(self, point):
        if os.environ.get("SC26_CRASH_HOOK") != "1":
            return
        f = self.dir / "crash_at"
        try:
            if f.read_text().strip() == point:
                f.unlink()
                os._exit(137)
        except FileNotFoundError:
            pass

    @staticmethod
    def meta(c, k):
        return c.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()[0]

    def halted(self, c):
        """the model's `s.halted ∧ C.haltCheck`"""
        return bool(self.meta(c, "halted")) and self.on["halt"]

    @staticmethod
    def set_meta(c, k, v):
        c.execute("UPDATE meta SET v=? WHERE k=?", (v, k))

    @staticmethod
    def trace(c, op, caller, args, accepted, result=None):
        c.execute("INSERT INTO trace(op,caller,args,accepted,result,t) VALUES(?,?,?,?,?,?)",
                  (op, caller, json.dumps(args, sort_keys=True), int(accepted),
                   None if result is None else json.dumps(result), time.time()))

    def txn(self, fn):
        c = self.conn()
        c.execute("BEGIN IMMEDIATE")
        try:
            out = fn(c)
            c.execute("COMMIT")
            return out
        except BaseException:
            c.execute("ROLLBACK")
            raise

    @staticmethod
    def req_tx(c, id):
        row = c.execute("SELECT requester, dest, amount, memo FROM requests WHERE id=?", (id,)).fetchone()
        return None if row is None else (row[0], tuple(row[1:]))

    # ---- model operations ----
    def request(self, uid, tx):
        def f(c):
            ok = not self.halted(c) and uid in self.agents
            if not ok:
                self.trace(c, "request", uid, {"tx": tx}, False)
                return None
            n = self.meta(c, "next")
            c.execute("INSERT INTO requests VALUES(?,?,?,?,?)", (n, uid, *tx))
            self.set_meta(c, "next", n + 1)
            self.trace(c, "request", uid, {"tx": tx}, True, n)
            return n
        n = self.txn(f)
        if n is None:
            raise Refused("request refused")
        return {"id": n}

    def approve(self, uid, id, tx):
        def f(c):
            r = self.req_tx(c, id)
            ok = (not self.halted(c) and r is not None and uid in self.approvers
                  and (not self.on["distinct"] or uid != r[0]) and (not self.on["payload"] or tx == r[1]))
            if ok:
                c.execute("INSERT INTO approvals(id,approver,dest,amount,memo) VALUES(?,?,?,?,?)", (id, uid, *tx))
            self.trace(c, "approve", uid, {"id": id, "tx": tx}, ok)
            return ok
        if not self.txn(f):
            raise Refused("approve refused")
        return "approved"

    def execute(self, uid, id):
        def f(c):
            r = self.req_tx(c, id)
            ok = False
            if not self.halted(c) and r is not None:
                spent = self.meta(c, "spent")
                ok = (c.execute("SELECT 1 FROM approvals WHERE id=?", (id,)).fetchone() is not None
                      and (not self.on["nonce"] or c.execute("SELECT 1 FROM reserved WHERE id=?", (id,)).fetchone() is None)
                      and (not self.on["cap"] or spent + r[1][1] <= self.meta(c, "cap")))
                if ok:
                    c.execute("INSERT OR IGNORE INTO reserved VALUES(?, (SELECT COALESCE(MAX(seq),0)+1 FROM reserved))",
                              (id,))
                    self.set_meta(c, "spent", spent + r[1][1])
            self.trace(c, "execute", uid, {"id": id}, ok)
            return ok
        if not self.txn(f):
            raise Refused("execute refused")
        self.hook("after_reserve")
        return {"reserved": True, "delivery": self.deliver(self.uid, id)}

    def deliver(self, uid, id, source=None):
        """the model's `deliver id` (send), logged before the bank is contacted. `dlock` (also taken by `halt`)
        covers the halt check and the send log only: a message already logged may still reach the bank after a
        HALT, exactly like the model's `arrive`."""
        with self.dlock:
            def f(c):
                r = self.req_tx(c, id)
                ok = (not self.halted(c) and r is not None
                      and c.execute("SELECT 1 FROM reserved WHERE id=?", (id,)).fetchone() is not None)
                args = {"id": id} if source is None else {"id": id, "source": source}
                self.trace(c, "deliver", uid, args, ok)
                if not ok:
                    return None
                cur = c.execute("INSERT INTO delivery(id) VALUES(?)", (id,))
                return cur.lastrowid, r[1]
            got = self.txn(f)
        if got is None:
            raise Refused("deliver refused")
        dseq, tx = got
        self.hook("after_intent_before_send")
        return self.complete(dseq, id, tx)

    def complete(self, dseq, id, tx):
        """transmit a logged message to the bank (the bank's processing is the model's `arrive`), then acknowledge"""
        try:
            reply = call(self.bank_socket, {"op": "transfer", "key": id, "dest": tx[0], "amount": tx[1],
                                            "memo": tx[2]})
        except OSError:
            return "pending"
        if not reply.get("ok"):
            return "pending"
        if reply["result"] == "conflict":
            # the bank holds a DIFFERENT payload under this key: a hard error, never marked delivered
            self.txn(lambda c: c.execute("UPDATE delivery SET outcome='conflict' WHERE seq=?", (dseq,)))
            return "conflict"
        self.hook("after_bank_ack")
        self.txn(lambda c: c.execute("UPDATE delivery SET acked=1, outcome=? WHERE seq=?", (reply["result"], dseq)))
        return reply["result"]

    def halt(self, uid):
        with self.dlock:
            def f(c):
                ok = uid in self.admins
                if ok:
                    self.set_meta(c, "halted", 1)
                self.trace(c, "halt", uid, {}, ok)
                return ok
            if not self.txn(f):
                raise Refused("halt refused")
        return "halted"

    def recover(self):
        """After a halt the gate initiates NO bank call: unsent or unacknowledged intents stay stranded (listed in
        `dump`). Otherwise: re-send every unacknowledged intent, then send every reservation that has none."""
        c = self.conn()
        if self.halted(c):
            return
        for dseq, id in c.execute("SELECT seq, id FROM delivery WHERE acked=0 ORDER BY seq").fetchall():
            with self.dlock:  # a re-send is a new transmission: it must not overlap or follow a committed halt
                if self.halted(c):
                    return
                self.complete(dseq, id, self.req_tx(c, id)[1])
        if not self.halted(c):
            todo = c.execute("SELECT id FROM reserved WHERE id NOT IN (SELECT id FROM delivery) ORDER BY seq").fetchall()
            for (id,) in todo:
                try:
                    self.deliver(self.uid, id, source="recovery")
                except Refused:
                    pass

    # ---- dispatch ----
    def dispatch(self, uid, req):
        op = req["op"]
        try:
            if op == "request":
                shape(req, {"tx"})
                return self.request(uid, tx_of(req["tx"]))
            if op == "approve":
                shape(req, {"id", "tx"})
                return self.approve(uid, nat(req["id"]), tx_of(req["tx"]))
            if op == "execute":
                shape(req, {"id"})
                return self.execute(uid, nat(req["id"]))
            if op == "deliver":
                shape(req, {"id"})
                return self.deliver(uid, nat(req["id"]))
            if op == "halt":
                shape(req, set())
                return self.halt(uid)
        except Refused as e:
            if str(e).endswith(" refused"):
                raise
            self.txn(lambda c: self.trace(c, "malformed", uid, {"op": op}, False))
            raise
        if op == "pending":
            shape(req, set())
            if uid not in self.approvers:
                raise Refused("approvers only")
            c = self.conn()
            rows = c.execute("SELECT id, requester, dest, amount, memo FROM requests WHERE id NOT IN "
                             "(SELECT id FROM approvals) ORDER BY id").fetchall()
            return [{"id": r[0], "requester": r[1], "tx": {"dest": r[2], "amount": r[3], "memo": r[4]}} for r in rows]
        if op == "dump":
            shape(req, set())
            if uid != self.auditor and uid not in self.admins:
                raise Refused("auditor only")
            c = self.conn()
            out = {"meta": dict(c.execute("SELECT k, v FROM meta").fetchall()), "gate_uid": self.uid,
                   "recovered": self.recovered}
            for t in ("requests", "approvals", "reserved", "delivery", "trace"):
                cur = c.execute(f"SELECT * FROM {t} ORDER BY 1")
                cols = [d[0] for d in cur.description]
                out[t] = [dict(zip(cols, r)) for r in cur.fetchall()]
            # intents never acknowledged (unsent at a crash, stranded by a halt, or a bank conflict)
            out["stranded"] = [d for d in out["delivery"] if not d["acked"]
                               and not any(e["id"] == d["id"] and e["acked"] for e in out["delivery"])]
            return out
        self.txn(lambda c: self.trace(c, "malformed", uid, {"op": op[:32]}, False))
        raise Refused("unknown op")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--state", required=True)
    p.add_argument("--socket", required=True)
    p.add_argument("--bank-socket", required=True)
    p.add_argument("--cap", type=int, required=True)
    for role in ("agents", "approvers", "admins"):
        p.add_argument("--" + role, required=True)
    p.add_argument("--auditor", type=int, required=True)
    p.add_argument("--disable-check", action="append", default=[],
                   choices=["distinct", "payload", "nonce", "cap", "halt"], help="TEST-ONLY negative control")
    a = p.parse_args()
    if a.disable_check and os.environ.get("SC26_NEGATIVE_CONTROL") != "1":
        raise SystemExit("--disable-check is a negative control; refusing without SC26_NEGATIVE_CONTROL=1")
    ids = {r: [int(x) for x in getattr(a, r).split(",")] for r in ("agents", "approvers", "admins")}
    if os.geteuid() == 0 or os.geteuid() in ids["agents"] + ids["approvers"] + ids["admins"]:
        raise SystemExit("gate must run under its own UID")
    g = Gate(a.state, a.cap, ids["agents"], ids["approvers"], ids["admins"], a.auditor, a.bank_socket,
             tuple(a.disable_check))
    srv = make_server(a.socket, g.dispatch)
    hold = Path(a.state) / "hold_recovery"
    if os.environ.get("SC26_CRASH_HOOK") == "1" and hold.exists():
        # test-only: serve first (so an admin can HALT a restarted gate) and run recovery once the harness releases
        t = threading.Thread(target=srv.serve_forever, daemon=True)
        t.start()
        while hold.exists():
            time.sleep(.02)
        g.recover()
        g.recovered = True
        t.join()
    else:
        g.recover()
        g.recovered = True
        srv.serve_forever()


if __name__ == "__main__":
    main()
