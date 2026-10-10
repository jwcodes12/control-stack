"""SQLite-backed reference gate: F1/F3/F4/F5/F7/F8.

The sole modeled release effect is an atomic row in releases. The code DOES
NOT itself execute, deploy or sandbox code, stop an OS process, anchor against
trusted-host rollback or guard any paths outside this service. Run the broker
under a trusted UID, not inside the agent; only SO_PEERCRED identities from
server.py are trustworthy. Direct Controller callers simulate trusted roles.
"""
from __future__ import annotations

import hashlib
import os
import re
import sqlite3
import stat
import time
from dataclasses import dataclass
from contextlib import closing
from pathlib import Path


class Denied(Exception):
    """A request was rejected before the modeled release effect."""


@dataclass(frozen=True)
class Principals:
    agents: frozenset[int]
    reviewers: frozenset[int]
    approvers: frozenset[int]
    admins: frozenset[int]

    def __post_init__(self):
        groups = (self.agents, self.reviewers, self.approvers, self.admins)
        if not all(g and all(type(x) is int and x >= 0 for x in g) for g in groups):
            raise ValueError("four explicit nonempty UID role sets required")
        if sum(map(len, groups)) != len(set().union(*groups)):
            raise ValueError("agent and trusted roles must be disjoint")

    def allows(self, uid, role):
        return type(uid) is int and uid in getattr(self, role, frozenset())


class Controller:
    def __init__(self, path: Path, principals: Principals, clock=None):
        self.path = Path(path)
        self.principals = principals
        self.clock = clock if clock is not None else time.time
        self._open().close()

    @classmethod
    def bootstrap(cls, path: Path, principals: Principals, global_cap: int, clock=None):
        if type(global_cap) is not int or global_cap <= 0:
            raise ValueError("positive global cap required")
        path = Path(path)
        if not path.parent.is_dir() or path.is_symlink():
            raise Denied("admin must prepare a trusted directory")
        parent = path.parent.stat()
        if parent.st_uid != os.geteuid() or parent.st_mode & 0o022:
            raise Denied("controller directory not owned/secured by broker")
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        os.close(fd)
        with closing(sqlite3.connect(path)) as db, db:
            db.execute("PRAGMA synchronous=FULL")
            db.executescript("""
            CREATE TABLE meta (id INTEGER PRIMARY KEY CHECK(id=1),
                global_cap INTEGER NOT NULL, halted INTEGER NOT NULL CHECK(halted IN (0,1)),
                spent INTEGER NOT NULL);
            CREATE TABLE artifacts (digest TEXT PRIMARY KEY, body BLOB NOT NULL);
            CREATE TABLE reviews (digest TEXT PRIMARY KEY, reviewer_uid INTEGER NOT NULL);
            CREATE TABLE approvals (nonce TEXT PRIMARY KEY, digest TEXT NOT NULL,
                destination TEXT NOT NULL, agent_uid INTEGER NOT NULL,
                lease_id TEXT NOT NULL, signer_uid INTEGER NOT NULL,
                expires INTEGER NOT NULL, used INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE leases (lease_id TEXT PRIMARY KEY, agent_uid INTEGER NOT NULL,
                budget INTEGER NOT NULL, used INTEGER NOT NULL DEFAULT 0,
                expires INTEGER NOT NULL, revoked INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE releases (id INTEGER PRIMARY KEY AUTOINCREMENT,
                digest TEXT NOT NULL, destination TEXT NOT NULL,
                agent_uid INTEGER NOT NULL, nonce TEXT UNIQUE NOT NULL,
                lease_id TEXT NOT NULL, cost INTEGER NOT NULL, created INTEGER NOT NULL);
            -- A deliberately narrow *real* effect: a content-bound SQLite append
            -- in the SAME transaction as approval consumption and budget charge.
            -- No filesystem/network/process effect is claimed.
            CREATE TABLE effect_records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                release_id INTEGER NOT NULL UNIQUE REFERENCES releases(id),
                digest TEXT NOT NULL, destination TEXT NOT NULL,
                body BLOB NOT NULL, created INTEGER NOT NULL);
            """)
            db.execute("INSERT INTO meta VALUES (1, ?, 0, 0)", (global_cap,))
        dirfd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(dirfd)
        finally:
            os.close(dirfd)
        return cls(path, principals, clock)

    def _open(self):
        db = None
        try:
            info = self.path.lstat()
            parent = self.path.parent.stat()
            if (parent.st_uid != os.geteuid() or parent.st_mode & 0o022 or
                    info.st_uid != os.geteuid()):
                raise Denied("controller state or parent not broker-owned")
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or info.st_mode & 0o077:
                raise Denied("missing or insecure SQLite state")
            db = sqlite3.connect(self.path.resolve().as_uri() + "?mode=rw",
                                 uri=True, timeout=15, isolation_level=None)
            db.execute("PRAGMA synchronous=FULL")
            db.execute("PRAGMA foreign_keys=ON")
            if db.execute("SELECT COUNT(*) FROM meta WHERE id=1").fetchone() != (1,):
                db.close()
                raise Denied("state is not initialized")
            return db
        except (OSError, sqlite3.Error) as e:
            if db is not None:
                db.close()
            raise Denied("controller state unavailable") from e

    def _role(self, uid, role):
        if not self.principals.allows(uid, role):
            raise Denied("OS principal not authorized for role")

    @staticmethod
    def _token(s):
        if type(s) is not str or re.fullmatch(r"[A-Za-z0-9_-]{1,80}", s) is None:
            raise Denied("invalid identifier")
        return s

    @staticmethod
    def _destination(s):
        if type(s) is not str or len(s) > 160 or re.fullmatch(r"[A-Za-z0-9_./-]+", s) is None:
            raise Denied("invalid destination")
        if s.startswith("/") or any(p in ("", ".", "..") for p in s.split("/")):
            raise Denied("unsafe destination")
        return s

    @staticmethod
    def _digest(s):
        if type(s) is not str or re.fullmatch("[0-9a-f]{64}", s) is None:
            raise Denied("invalid content digest")
        return s

    def _now(self):
        n = int(self.clock())
        if n < 0:
            raise Denied("trusted time unavailable")
        return n

    def _tx(self, fn):
        db = self._open()
        try:
            db.execute("BEGIN IMMEDIATE")
            meta = db.execute("SELECT global_cap,halted,spent FROM meta WHERE id=1").fetchone()
            if meta is None or meta[1]:
                raise Denied("controller halted or state invalid")
            value = fn(db, meta)
            db.commit()
            return value
        except sqlite3.Error as e:
            db.rollback()
            raise Denied("trusted state transaction failed closed") from e
        except (Denied, ValueError, TypeError, OverflowError) as e:
            db.rollback()
            if isinstance(e, Denied):
                raise
            raise Denied("operation refused; transaction rolled back") from e
        finally:
            db.close()

    def stage(self, uid, body: bytes):
        self._role(uid, "agents")
        if type(body) is not bytes or len(body) > 1024 * 1024:
            raise Denied("artifact must be bytes no larger than 1MiB")
        digest = hashlib.sha256(body).hexdigest()
        def apply(db, _):
            old = db.execute("SELECT body FROM artifacts WHERE digest=?", (digest,)).fetchone()
            if old is not None and old[0] != body:
                raise Denied("digest collision")
            db.execute("INSERT OR IGNORE INTO artifacts VALUES (?, ?)", (digest, body))
            return digest
        return self._tx(apply)

    def review(self, uid, digest):
        self._role(uid, "reviewers")
        digest = self._digest(digest)
        def apply(db, _):
            if db.execute("SELECT 1 FROM artifacts WHERE digest=?", (digest,)).fetchone() is None:
                raise Denied("artifact missing")
            db.execute("INSERT OR REPLACE INTO reviews VALUES (?, ?)", (digest, uid))
            return True
        return self._tx(apply)

    def issue_lease(self, uid, lease_id, agent_uid, budget, expires):
        self._role(uid, "admins")
        lease_id = self._token(lease_id)
        self._role(agent_uid, "agents")
        if type(budget) is not int or budget <= 0 or type(expires) is not int or expires <= self._now():
            raise Denied("invalid budget or expiry")
        def apply(db, _):
            db.execute("INSERT INTO leases (lease_id,agent_uid,budget,expires) VALUES (?,?,?,?)",
                       (lease_id, agent_uid, budget, expires))
            return True
        return self._tx(apply)

    def approve(self, uid, nonce, digest, destination, agent_uid, lease_id, expires):
        self._role(uid, "approvers")
        nonce, digest, destination, lease_id = (self._token(nonce), self._digest(digest),
             self._destination(destination), self._token(lease_id))
        self._role(agent_uid, "agents")
        if type(expires) is not int or expires <= self._now():
            raise Denied("approval expiry must be in the future")
        def apply(db, _):
            review = db.execute("SELECT reviewer_uid FROM reviews WHERE digest=?", (digest,)).fetchone()
            lease = db.execute("SELECT agent_uid,expires,revoked FROM leases WHERE lease_id=?",
                               (lease_id,)).fetchone()
            if review is None or review[0] == uid or not self.principals.allows(review[0], "reviewers"):
                raise Denied("distinct trusted review required")
            if lease is None or lease[0] != agent_uid or lease[1] <= self._now() or lease[2]:
                raise Denied("active lease bound to agent required")
            db.execute("INSERT INTO approvals (nonce,digest,destination,agent_uid,lease_id,signer_uid,expires) VALUES (?,?,?,?,?,?,?)",
                       (nonce, digest, destination, agent_uid, lease_id, uid, expires))
            return True
        return self._tx(apply)

    def revoke(self, uid, lease_id):
        self._role(uid, "admins")
        lease_id = self._token(lease_id)
        def apply(db, _):
            if db.execute("UPDATE leases SET revoked=1 WHERE lease_id=?", (lease_id,)).rowcount != 1:
                raise Denied("unknown lease")
            return True
        return self._tx(apply)

    def release(self, uid, nonce, digest, destination, lease_id, cost=1, *, record_effect=False):
        """Atomic one-use admission. Optional effect is ONLY a SQLite body append.

        The effect and approval consumption commit together. This is NOT an
        OS-effect adaptor, not an external idempotent receiver, and does not
        guarantee another resource is mediated.
        """
        if type(record_effect) is not bool:
            raise Denied("invalid effect mode")
        self._role(uid, "agents")
        nonce, digest, destination, lease_id = (self._token(nonce), self._digest(digest),
            self._destination(destination), self._token(lease_id))
        if type(cost) is not int or cost < 1:
            raise Denied("trusted metering requires positive work units")
        def apply(db, meta):
            approval = db.execute("SELECT digest,destination,agent_uid,lease_id,signer_uid,expires,used FROM approvals WHERE nonce=?",
                                  (nonce,)).fetchone()
            if (approval is None or approval !=
                (digest, destination, uid, lease_id, approval[4], approval[5], 0)
                or approval[5] <= self._now()
                or not self.principals.allows(approval[4], "approvers")):
                raise Denied("unapproved, expired, forged or already-used request")
            lease = db.execute("SELECT agent_uid,budget,used,expires,revoked FROM leases WHERE lease_id=?",
                               (lease_id,)).fetchone()
            if (lease is None or lease[0] != uid or lease[4] or lease[3] <= self._now()
                or lease[2] + cost > lease[1] or meta[2] + cost > meta[0]):
                raise Denied("rejected lease, expiry, revocation or budget")
            body = db.execute("SELECT body FROM artifacts WHERE digest=?", (digest,)).fetchone()
            review = db.execute("SELECT reviewer_uid FROM reviews WHERE digest=?", (digest,)).fetchone()
            if body is None or hashlib.sha256(body[0]).hexdigest() != digest or review is None:
                raise Denied("artifact or reviewed digest no longer valid")
            db.execute("UPDATE leases SET used=used+? WHERE lease_id=?", (cost, lease_id))
            db.execute("UPDATE meta SET spent=spent+? WHERE id=1", (cost,))
            db.execute("UPDATE approvals SET used=1 WHERE nonce=?", (nonce,))
            cur = db.execute("INSERT INTO releases (digest,destination,agent_uid,nonce,lease_id,cost,created) VALUES (?,?,?,?,?,?,?)",
                             (digest, destination, uid, nonce, lease_id, cost, self._now()))
            if record_effect:
                # The only implemented effect is this exact reviewed byte string
                # written to the trusted SQLite DB in the SAME transaction.
                db.execute("INSERT INTO effect_records (release_id,digest,destination,body,created) VALUES (?,?,?,?,?)",
                           (cur.lastrowid, digest, destination, body[0], self._now()))
            return cur.lastrowid
        return self._tx(apply)

    def halt(self, uid):
        self._role(uid, "admins")
        db = self._open()
        try:
            db.execute("BEGIN IMMEDIATE")
            db.execute("UPDATE meta SET halted=1 WHERE id=1")
            db.commit()
            return True
        except sqlite3.Error as e:
            db.rollback()
            raise Denied("halt persistence unavailable") from e
        finally:
            db.close()

    def state(self, uid):
        if not any(self.principals.allows(uid, x) for x in ("agents", "reviewers", "approvers", "admins")):
            raise Denied("not authorized")
        db = self._open()
        try:
            meta = db.execute("SELECT global_cap,halted,spent FROM meta WHERE id=1").fetchone()
            releases = db.execute("SELECT COUNT(*) FROM releases").fetchone()[0]
            return {"global_cap": meta[0], "halted": bool(meta[1]), "spent": meta[2],
                    "releases": releases}
        finally:
            db.close()
