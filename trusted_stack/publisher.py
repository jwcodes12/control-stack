"""Linux-only, narrowly scoped file effect receiver for approved SQLite outbox rows.

The effect path is broker-configured, not supplied by an agent. Only the
admin UID can publish. No code execution, network effect, or universal
mediation is claimed. Link-without-replace makes each output idempotent.
"""
import hashlib
import os
import sqlite3
import stat
from pathlib import Path
from .controller import Denied

def _same(fd, name, body):
    try:
        f = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=fd)
    except FileNotFoundError:
        return False
    try:
        s = os.fstat(f)
        if not stat.S_ISREG(s.st_mode) or s.st_uid != os.geteuid() or s.st_mode & 0o077 or s.st_nlink != 1 or s.st_size != len(body):
            raise Denied("conflicting output metadata")
        chunks = []
        remaining = len(body)
        while remaining:
            chunk = os.read(f, min(remaining, 65536))
            if not chunk:
                raise Denied("truncated output")
            chunks.append(chunk)
            remaining -= len(chunk)
        if b"".join(chunks) != body:
            raise Denied("conflicting output contents")
        return True
    finally:
        os.close(f)

def _write_once(fd, release_id, body):
    name = f"effect-{release_id:012d}.bin"
    if _same(fd, name, body):
        return name
    temp = f".effect-{release_id:012d}-{os.urandom(16).hex()}.tmp"
    created = False
    try:
        f = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                    0o600, dir_fd=fd)
        created = True
        try:
            offset = 0
            while offset < len(body):
                offset += os.write(f, body[offset:])
            os.fsync(f)
        finally:
            os.close(f)
        try:
            os.link(temp, name, src_dir_fd=fd, dst_dir_fd=fd,
                    follow_symlinks=False)
        except FileExistsError:
            if not _same(fd, name, body):
                raise Denied("publication conflict")
        os.unlink(temp, dir_fd=fd)
        created = False
        os.fsync(fd)
        if not _same(fd, name, body):
            raise Denied("publication verification failed")
        return name
    finally:
        if created:
            try:
                os.unlink(temp, dir_fd=fd)
            except FileNotFoundError:
                pass

def publish_effect(controller, uid, release_id, effect_root):
    """Serialize publication with HALT/revocation using SQLite's write lock.

    Crash after output link but before response: a retry verifies the fixed
    filename and exact bytes; it never creates a second external effect.
    Depends on exclusive trusted UID/root and durable host fsync semantics.
    """
    controller._role(uid, "admins")
    if type(release_id) is not int or release_id < 1:
        raise Denied("invalid release identifier")
    fd, db = None, None
    try:
        fd = os.open(Path(effect_root), os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        st = os.fstat(fd)
        if st.st_uid != os.geteuid() or st.st_mode & 0o077:
            raise Denied("effect root must be private and broker owned")
        db = controller._open()
        db.execute("BEGIN IMMEDIATE")
        if db.execute("SELECT halted FROM meta WHERE id=1").fetchone() != (0,):
            raise Denied("HALT blocks new publication")
        row = db.execute("""
            SELECT e.body, e.digest, e.destination,
                   r.digest, r.destination, r.agent_uid,
                   a.agent_uid, a.used, a.expires,
                   l.agent_uid, l.revoked, l.expires
            FROM effect_records e
            JOIN releases r ON r.id=e.release_id
            JOIN approvals a ON a.nonce=r.nonce
            JOIN leases l ON l.lease_id=r.lease_id
            WHERE e.release_id=?
        """, (release_id,)).fetchone()
        if row is None:
            raise Denied("committed effect record unavailable")
        body, digest, dest, rd, rdest, ra, aa, used, ae, la, revoked, le = row
        if (type(body) is not bytes or hashlib.sha256(body).hexdigest() != digest
            or digest != rd or dest != rdest or ra != aa or ra != la
            or used != 1 or revoked != 0 or min(ae, le) <= controller._now()):
            raise Denied("approval, lease or bytes invalid")
        name = _write_once(fd, release_id, body)
        db.commit()
        return {"file": name, "digest": digest, "release_id": release_id}
    except (OSError, sqlite3.Error, ValueError, TypeError) as e:
        if db is not None:
            db.rollback()
        raise Denied("filesystem materialization denied; reconcile before retry") from e
    except Denied:
        if db is not None:
            db.rollback()
        raise
    finally:
        if db is not None:
            db.close()
        if fd is not None:
            os.close(fd)
