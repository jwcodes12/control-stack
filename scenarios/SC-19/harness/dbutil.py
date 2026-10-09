#!/usr/bin/env python3
"""SC-19 two-phase destructive ops: shared SQLite helpers (prereg/SC19-TWO-PHASE.md).

Schema of the disposable "production" DB:
  objs(target TEXT, id INTEGER, payload BLOB, PRIMARY KEY(target, id))
  versions(target TEXT PRIMARY KEY, ver INTEGER)        -- bumped by every write to a target
  history(seq INTEGER PRIMARY KEY AUTOINCREMENT, target TEXT, ver_after INTEGER, kind TEXT, rows_changed INTEGER,
          rows_hash TEXT, t_ns INTEGER)                  -- the DB's own history, written in the same transaction
Imported by the harness processes (they run with -I -S; the runner puts this directory on their path explicitly).
"""
import hashlib
import sqlite3
import time

SCHEMA = """
CREATE TABLE IF NOT EXISTS objs(target TEXT, id INTEGER, payload BLOB, PRIMARY KEY(target, id));
CREATE TABLE IF NOT EXISTS versions(target TEXT PRIMARY KEY, ver INTEGER);
CREATE TABLE IF NOT EXISTS history(seq INTEGER PRIMARY KEY AUTOINCREMENT, target TEXT, ver_after INTEGER, kind TEXT,
                                   rows_changed INTEGER, rows_hash TEXT, t_ns INTEGER);
"""


def connect(path):
    c = sqlite3.connect(path, timeout=10.0, isolation_level=None)
    c.execute("PRAGMA synchronous=FULL")
    return c


def rows_hash(rows):
    h = hashlib.sha256()
    for i, p in sorted(rows):
        h.update(b"%d:" % i + hashlib.sha256(bytes(p)).digest())
    return h.hexdigest()


def target_rows(c, t):
    return [(int(i), bytes(p)) for i, p in c.execute("SELECT id, payload FROM objs WHERE target=? ORDER BY id", (t,))]


def version(c, t):
    r = c.execute("SELECT ver FROM versions WHERE target=?", (t,)).fetchone()
    return int(r[0]) if r else 0


def summary(c):
    """per-target {ver, count, hash} of a DB (prod or a snapshot copy)"""
    out = {}
    ts = {r[0] for r in c.execute("SELECT target FROM versions")} | {r[0] for r in c.execute("SELECT DISTINCT target FROM objs")}
    for t in sorted(ts):
        rows = target_rows(c, t)
        out[t] = {"ver": version(c, t), "count": len(rows), "hash": rows_hash(rows)}
    return out


def write_rows(c, t, n, kind="write"):
    """inside an open IMMEDIATE transaction: add n rows to target t, bump its version, record history"""
    nxt = c.execute("SELECT COALESCE(MAX(id), -1) + 1 FROM objs WHERE target=?", (t,)).fetchone()[0]
    rows = [(nxt + k, ("object %s/%d version-independent payload " % (t, nxt + k)).encode() * 4) for k in range(n)]
    c.executemany("INSERT INTO objs(target, id, payload) VALUES (?, ?, ?)", [(t, i, p) for i, p in rows])
    v = version(c, t) + 1
    c.execute("INSERT OR REPLACE INTO versions(target, ver) VALUES (?, ?)", (t, v))
    c.execute("INSERT INTO history(target, ver_after, kind, rows_changed, rows_hash, t_ns) VALUES (?,?,?,?,?,?)",
              (t, v, kind, n, rows_hash(rows), time.monotonic_ns()))
    return v
