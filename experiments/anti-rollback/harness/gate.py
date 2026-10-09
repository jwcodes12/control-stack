#!/usr/bin/env python3
"""Anti-rollback gate: a small budget + nonce ledger in SQLite bound to an external monotonic anchor (Python 3.9).

Store (gate.sqlite3, journal_mode=DELETE, synchronous=FULL):
  meta(version, digest, spent)   journal(version, op, digest)   nonces(nonce, amount, version)
  digest chain: d_0 = 64 zeros, d_v = sha256(d_{v-1} || op_v), with op_v the canonical JSON of the operation.
Effects: an append-only `effects.log` OUTSIDE the store (it is not part of any snapshot), one line per landed spend,
performed unconditionally on the normal path; crash recovery re-performs a missing effect deduplicated by (version,
digest), so it lands exactly once.

Every operation (and startup) compares the store's (version, digest) with the anchor:
  equal                                   -> OK (an effect missing for the current version is re-performed)
  store = anchor + 1, chain valid, and the store's digest at `anchor.version` equals the anchor's digest
                                          -> crash window after commit, before the anchor increment: RECOVER by
                                             incrementing the anchor and re-performing the effect
  anything else (older store, forked digest, gap)
                                          -> ROLLBACK: fail closed, every later operation refused
A spend: refuse unless OK; refuse a used nonce; refuse if spent + amount > cap; then commit store (v+1), then
increment the anchor, then perform the effect. Crash points (for the harness): after_commit, after_anchor, after_effect.

`anchor_enabled=False` is the NEGATIVE CONTROL: no anchor read, compare or increment.
"""
import argparse
import hashlib
import json
import os
import socket
import sqlite3
import struct
import sys

GENESIS = "0" * 64


class Refused(Exception):
    pass


def chain(prev, op):
    return hashlib.sha256((prev + op).encode()).hexdigest()


class GateCore:
    def __init__(self, db_path, effects_path, anchor, cap, anchor_enabled=True, crash_file=None):
        self.anchor, self.cap, self.anchor_enabled = anchor, cap, anchor_enabled
        self.effects_path, self.crash_file = effects_path, crash_file
        self.db = sqlite3.connect(db_path, isolation_level=None)
        self.db.execute("PRAGMA journal_mode=DELETE")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.executescript(
            "CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT NOT NULL);"
            "CREATE TABLE IF NOT EXISTS journal(version INTEGER PRIMARY KEY, op TEXT NOT NULL, digest TEXT NOT NULL);"
            "CREATE TABLE IF NOT EXISTS nonces(nonce TEXT PRIMARY KEY, amount INTEGER NOT NULL, version INTEGER);")
        if self._meta("version") is None:
            self.db.execute("BEGIN IMMEDIATE")
            for k, v in (("version", "0"), ("digest", GENESIS), ("spent", "0")):
                self.db.execute("INSERT INTO meta VALUES(?,?)", (k, v))
            self.db.execute("COMMIT")
        self.status, self.recovered, self.detail = "ok", None, None
        self.startup()

    # ---- store
    def _meta(self, k):
        r = self.db.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
        return r[0] if r else None

    def store_state(self):
        return int(self._meta("version")), self._meta("digest"), int(self._meta("spent"))

    def chain_ok(self):
        rows = self.db.execute("SELECT version, op, digest FROM journal ORDER BY version").fetchall()
        d = GENESIS
        for i, (v, op, dig) in enumerate(rows, 1):
            if v != i or chain(d, op) != dig:
                return False
            d = dig
        return d == self._meta("digest") and len(rows) == int(self._meta("version"))

    def digest_at(self, v):
        if v == 0:
            return GENESIS
        r = self.db.execute("SELECT digest FROM journal WHERE version=?", (v,)).fetchone()
        return r[0] if r else None

    # ---- effects (outside the store)
    def effects(self):
        try:
            with open(self.effects_path) as f:
                return [json.loads(l) for l in f if l.strip()]
        except FileNotFoundError:
            return []

    def effect(self, v, digest, nonce, amount, dedupe=False):
        """perform the side effect. The normal path always performs it (a real gate would just pay); only crash
        recovery deduplicates, by (version, digest), so a re-performed effect lands at most once"""
        if dedupe and any(e["version"] == v and e["digest"] == digest for e in self.effects()):
            return False
        fd = os.open(self.effects_path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
        try:
            os.write(fd, (json.dumps({"version": v, "digest": digest, "nonce": nonce, "amount": amount}) + "\n").encode())
            os.fsync(fd)
        finally:
            os.close(fd)
        return True

    def ensure_effect(self, v):
        r = self.db.execute("SELECT op, digest FROM journal WHERE version=?", (v,)).fetchone() if v else None
        if r is None:
            return False
        o = json.loads(r[0])
        return self.effect(v, r[1], o["nonce"], o["amount"], dedupe=True)

    def crash(self, point):
        if self.crash_file and os.path.exists(self.crash_file):
            with open(self.crash_file) as f:
                want = f.read().strip()
            if want == point:
                os.unlink(self.crash_file)
                os._exit(17)

    # ---- anchor agreement
    def check(self):
        """compare store and anchor; recover the crash window; otherwise fail closed"""
        if not self.anchor_enabled or self.status != "ok":
            return
        v, d, _ = self.store_state()
        a = self.anchor.read()
        if (v, d) == (a["version"], a["digest"]):
            if self.ensure_effect(v):
                self.recovered = {"kind": "effect_reperformed", "version": v}
            return
        if v == a["version"] + 1 and self.chain_ok() and self.digest_at(a["version"]) == a["digest"]:
            self.anchor.increment(v, d)
            self.ensure_effect(v)
            self.recovered = {"kind": "anchor_incremented", "version": v}
            return
        self.status = "rollback"
        self.detail = {"store": [v, d], "anchor": [a["version"], a["digest"]]}

    def startup(self):
        if self.anchor_enabled and not self.chain_ok():
            self.status, self.detail = "rollback", {"chain": "invalid"}
            return
        self.check()

    # ---- operation
    def spend(self, nonce, amount):
        if type(nonce) is not str or not 0 < len(nonce) <= 64 or type(amount) is not int or amount <= 0:
            raise Refused("malformed")
        self.check()
        if self.status != "ok":
            raise Refused("fail closed: " + self.status)
        v, d, spent = self.store_state()
        if self.db.execute("SELECT 1 FROM nonces WHERE nonce=?", (nonce,)).fetchone():
            raise Refused("nonce already used")
        if spent + amount > self.cap:
            raise Refused("budget exceeded")
        op = json.dumps({"nonce": nonce, "amount": amount}, sort_keys=True)
        nv, nd = v + 1, chain(d, op)
        self.db.execute("BEGIN IMMEDIATE")
        self.db.execute("INSERT INTO nonces VALUES(?,?,?)", (nonce, amount, nv))
        self.db.execute("INSERT INTO journal VALUES(?,?,?)", (nv, op, nd))
        for k, val in (("version", str(nv)), ("digest", nd), ("spent", str(spent + amount))):
            self.db.execute("UPDATE meta SET v=? WHERE k=?", (val, k))
        self.db.execute("COMMIT")
        self.crash("after_commit")
        if self.anchor_enabled:
            self.anchor.increment(nv, nd)
        self.crash("after_anchor")
        self.effect(nv, nd, nonce, amount)
        self.crash("after_effect")
        return {"version": nv}


class AnchorClient:
    def __init__(self, path):
        self.path = path

    def _call(self, req):
        with socket.socket(socket.AF_UNIX) as s:
            s.settimeout(5)
            s.connect(self.path)
            s.sendall((json.dumps(req) + "\n").encode())
            buf = b""
            while not buf.endswith(b"\n"):
                part = s.recv(4096)
                if not part:
                    break
                buf += part
        r = json.loads(buf)
        if not r.get("ok"):
            raise Refused("anchor: " + str(r.get("error")))
        return r["result"]

    def read(self):
        return self._call({"op": "read"})

    def increment(self, to, digest):
        return self._call({"op": "increment", "to": to, "digest": digest})


def peer_uid(conn):
    return struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True)
    ap.add_argument("--effects", required=True)
    ap.add_argument("--socket", required=True)
    ap.add_argument("--anchor-socket", required=True)
    ap.add_argument("--cap", type=int, required=True)
    ap.add_argument("--client-uid", type=int, required=True)
    ap.add_argument("--anchor-off", action="store_true", help="NEGATIVE CONTROL only")
    a = ap.parse_args()
    if a.anchor_off and os.environ.get("AR_NEGATIVE_CONTROL") != "1":
        sys.exit("--anchor-off needs AR_NEGATIVE_CONTROL=1")
    g = GateCore(os.path.join(a.state, "gate.sqlite3"), a.effects, AnchorClient(a.anchor_socket), a.cap,
                 anchor_enabled=not a.anchor_off, crash_file=os.path.join(a.state, "crash_at"))
    if os.path.exists(a.socket):
        os.unlink(a.socket)
    srv = socket.socket(socket.AF_UNIX)
    srv.bind(a.socket)
    os.chmod(a.socket, 0o666)
    srv.listen(16)
    sys.stdout.write("READY " + json.dumps({"status": g.status, "recovered": g.recovered,
                                            "version": g.store_state()[0]}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = srv.accept()
        with conn:
            try:
                uid = peer_uid(conn)
                conn.settimeout(5)
                buf = b""
                while not buf.endswith(b"\n") and len(buf) < 4096:
                    part = conn.recv(4096)
                    if not part:
                        break
                    buf += part
                req = json.loads(buf)
                if req.get("op") == "spend" and uid == a.client_uid and set(req) == {"op", "nonce", "amount"}:
                    reply = {"ok": True, "result": g.spend(req["nonce"], req["amount"])}
                elif req.get("op") == "status" and set(req) == {"op"} and uid == a.client_uid:
                    g.check()
                    v, d, spent = g.store_state()
                    reply = {"ok": True, "result": {"status": g.status, "version": v, "digest": d, "spent": spent}}
                else:
                    reply = {"ok": False, "error": "refused"}
            except Refused as e:
                reply = {"ok": False, "error": str(e)}
            except (ValueError, OSError, sqlite3.Error) as e:
                reply = {"ok": False, "error": "error: " + type(e).__name__}
            try:
                conn.sendall((json.dumps(reply) + "\n").encode())
            except OSError:
                pass


if __name__ == "__main__":
    main()
