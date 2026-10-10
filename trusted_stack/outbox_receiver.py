"""Crash-recoverable, narrow trusted local-file receiver for committed effect_records.

This is a REAL local filesystem byte publication, NOT a universal syscall gate.
Never expose deliver_record as an untrusted-agent RPC. The process invoking it
must be the trusted controller DB owner AND a configured admin OS UID.
"""
from __future__ import annotations

import hashlib
import os
import re
import secrets
import sqlite3
import stat
from pathlib import Path

from trusted_stack.controller import Controller, Denied

MAX_BODY = 1024 * 1024
_FILE_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC
_DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC


def _read_verified(dirfd: int, name: str, expected: bytes, *, links: int = 1) -> None:
    try:
        fd = os.open(name, _FILE_FLAGS, dir_fd=dirfd)
    except FileNotFoundError as exc:
        raise Denied("previously published receiver file is missing") from exc
    except OSError as exc:
        raise Denied("receiver file cannot be safely opened") from exc
    try:
        info = os.fstat(fd)
        if (not stat.S_ISREG(info.st_mode) or info.st_nlink != links
                or info.st_uid != os.geteuid() or info.st_mode & 0o077
                or info.st_size != len(expected) or info.st_size > MAX_BODY):
            raise Denied("receiver file metadata differs from trusted record")
        data = bytearray()
        while len(data) <= MAX_BODY:
            part = os.read(fd, 65536)
            if not part:
                break
            data.extend(part)
        if bytes(data) != expected:
            raise Denied("receiver file content differs from trusted record")
    finally:
        os.close(fd)


def _recover_interrupted_link_cleanup(dirfd: int, name: str, expected: bytes) -> None:
    """Recover ONLY the post-link/pre-unlink crash state under a private owner.

    Both names must be the exact same verified regular inode, and precisely
    one trusted randomly named temporary link must remain. A third hardlink,
    content mismatch, suspicious symlink or ambiguous debris is a denial.
    This assumes no untrusted actor can mutate the private trusted directory.
    """
    _read_verified(dirfd, name, expected, links=2)
    published = os.stat(name, dir_fd=dirfd, follow_symlinks=False)
    matches = []
    for candidate in os.listdir(dirfd):
        if re.fullmatch(r"\.pending-[0-9a-f]{32}", candidate) is None:
            continue
        try:
            info = os.stat(candidate, dir_fd=dirfd, follow_symlinks=False)
        except FileNotFoundError as exc:
            raise Denied("receiver directory changed during reconciliation") from exc
        if info.st_dev == published.st_dev and info.st_ino == published.st_ino:
            matches.append(candidate)
    if len(matches) != 1:
        raise Denied("cannot identify a unique interrupted temporary hardlink")
    os.unlink(matches[0], dir_fd=dirfd)
    os.fsync(dirfd)
    _read_verified(dirfd, name, expected)


def _publish(dirfd: int, name: str, body: bytes) -> None:
    """Atomic no-overwrite name publication, durable before SQLite receipt."""
    temp = ".pending-" + secrets.token_hex(16)
    fd = None
    try:
        fd = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=dirfd)
        remaining = memoryview(body)
        while remaining:
            n = os.write(fd, remaining)
            if n <= 0:
                raise OSError("short write")
            remaining = remaining[n:]
        os.fsync(fd)
        os.close(fd)
        fd = None
        try:
            # Hard-link publish is atomic and does not replace an existing name.
            os.link(temp, name, src_dir_fd=dirfd, dst_dir_fd=dirfd,
                    follow_symlinks=False)
        except FileExistsError:
            _read_verified(dirfd, name, body)
        os.fsync(dirfd)
    finally:
        if fd is not None:
            os.close(fd)
        try:
            os.unlink(temp, dir_fd=dirfd)
        except FileNotFoundError:
            pass
        # Persist removal of the temporary hardlink. Without this second
        # directory fsync, power loss could resurrect it and leave a valid
        # published file with st_nlink=2, triggering fail-closed on restart.
        os.fsync(dirfd)


def deliver_record(controller: Controller, release_id: int, output_dir: Path,
                   *, after_publish=None) -> str:
    """Publish one previously committed reviewed artifact under <id>.body.

    DB writer lock linearizes with HALT. If killed after filesystem publication
    but before the DB receipt commits, retry verifies the old file rather than
    executing a second effect. A HALT occurring after that crash may leave the
    file present and receipt absent, correctly recording the in-flight gap.
    after_publish is a local, trusted test fault hook, not exposed by server.py.
    """
    if not controller.principals.allows(os.geteuid(), "admins"):
        raise Denied("only the actual trusted admin OS UID may deliver")
    if type(release_id) is not int or release_id <= 0 or release_id > 2**63 - 1:
        raise Denied("invalid release identifier")
    try:
        dirfd = os.open(os.fspath(output_dir), _DIR_FLAGS)
    except (OSError, TypeError) as exc:
        raise Denied("trusted receiver directory unavailable") from exc
    try:
        info = os.fstat(dirfd)
        if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid()
                or info.st_mode & 0o077):
            raise Denied("receiver directory must be private and broker-owned")
        db = controller._open()
        try:
            db.execute("BEGIN IMMEDIATE")
            if db.execute("SELECT halted FROM meta WHERE id=1").fetchone() != (0,):
                raise Denied("HALT blocks even pending external delivery")
            row = db.execute(
                """SELECT e.digest, e.destination, e.body,
                          r.digest, r.destination, r.nonce,
                          r.agent_uid, r.lease_id
                   FROM effect_records e
                   JOIN releases r ON r.id=e.release_id
                   WHERE e.release_id=?""", (release_id,)).fetchone()
            if row is None:
                raise Denied("no committed effect record for release")
            (digest, destination, body, release_digest, release_dest, nonce,
             release_agent, release_lease) = row
            # An admission is not a perpetual authorization to dispatch.
            # Bind the persisted release to the *same exact* approval, agent,
            # reviewed artifact, destination and lease. Checking only the
            # nonce or the approver's role would leave a confused-deputy gap.
            approval = db.execute(
                """SELECT digest, destination, agent_uid, lease_id,
                          signer_uid, expires, used
                   FROM approvals WHERE nonce=?""", (nonce,)).fetchone()
            if (approval is None or approval[:4] !=
                    (digest, destination, release_agent, release_lease) or
                    approval[6] != 1 or
                    not controller.principals.allows(approval[4], "approvers") or
                    not controller.principals.allows(release_agent, "agents")):
                raise Denied("delivery approval/release binding is invalid")
            grant = db.execute(
                "SELECT grantor_uid,delegate_uid,revoked FROM delegations WHERE nonce=?",
                (nonce,)).fetchone()
            executed = db.execute(
                """SELECT nonce,grantor_uid,delegate_uid
                   FROM delegated_releases WHERE release_id=?""",
                (release_id,)).fetchone()
            if grant is None:
                if executed is not None:
                    raise Denied("unjustified delegated executor receipt")
            elif (grant[0] != release_agent or grant[2] != 0 or
                  executed != (nonce, release_agent, grant[1]) or
                  not controller.principals.allows(grant[1], "agents")):
                raise Denied("delegated effect grant revoked or provenance invalid")
            lease = db.execute(
                "SELECT agent_uid, expires, revoked FROM leases WHERE lease_id=?",
                (release_lease,)).fetchone()
            checked_at = controller._now()
            if (lease is None or lease[0] != release_agent or lease[2] or
                    approval[5] <= checked_at or lease[1] <= checked_at):
                raise Denied("external delivery revoked or expired")
            review = db.execute(
                "SELECT reviewer_uid FROM reviews WHERE digest=?",
                (digest,)).fetchone()
            if (review is None or
                    not controller.principals.allows(review[0], "reviewers") or
                    type(body) is not bytes or len(body) > MAX_BODY or
                    digest != hashlib.sha256(body).hexdigest() or
                    digest != release_digest or destination != release_dest):
                raise Denied("release and reviewed effect are inconsistent")
            db.execute("""CREATE TABLE IF NOT EXISTS delivery_receipts (
                       release_id INTEGER PRIMARY KEY REFERENCES releases(id),
                       digest TEXT NOT NULL, destination TEXT NOT NULL)""")
            receipt = db.execute(
                "SELECT digest, destination FROM delivery_receipts WHERE release_id=?",
                (release_id,)).fetchone()
            name = str(release_id) + ".body"
            if receipt is not None:
                if receipt != (digest, destination):
                    raise Denied("durable delivery receipt disagrees")
                _read_verified(dirfd, name, body)
            else:
                try:
                    _read_verified(dirfd, name, body)
                except Denied as exc:
                    # ONLY missing files may be newly published. Any different
                    # preexisting bytes, symlink, or metadata mismatch fails shut.
                    if not isinstance(exc.__cause__, FileNotFoundError):
                        _recover_interrupted_link_cleanup(dirfd, name, body)
                    else:
                        _publish(dirfd, name, body)
                if after_publish is not None:
                    after_publish()
                db.execute(
                    "INSERT INTO delivery_receipts VALUES (?,?,?)",
                    (release_id, digest, destination))
            db.commit()
            return name
        except (sqlite3.Error, OSError) as exc:
            db.rollback()
            raise Denied("trusted local delivery failed closed") from exc
        except BaseException:
            db.rollback()
            raise
        finally:
            db.close()
    finally:
        os.close(dirfd)
