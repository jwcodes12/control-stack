"""Unix peer-credential broker for trusted_stack.Controller.

The broker alone owns the 0600 database and derives caller UID from
SO_PEERCRED; never pass caller-supplied identity in a request. This is a
reference interface, not a network-facing or production authorization server.
"""
import argparse
import base64
import contextlib
import json
import os
import socket
import stat
import struct
import threading
import time
from pathlib import Path
from .controller import Controller, Denied, Principals
from .publisher import publish_effect

MAX_REQUEST = 1500000
READ_DEADLINE = 3.0         # seconds to receive one whole frame
PER_UID_CONNECTIONS = 2     # concurrent connections one caller UID may hold
MAX_CONNECTIONS = 12        # below the listen backlog
RESERVED_FOR_TRUSTED = 4    # of those, slots only reviewer/approver/admin UIDs may use, so agents and strangers cannot starve HALT
DELEGATION_OPS = {"delegate", "revoke_delegation"}


def run_one(controller, uid, req, allow_delegation=True, *, effect_root=None):
    """allow_delegation defaults on for the library and its delegated-model tests; the command line turns it off
    unless --allow-delegation is given (the reference deployment profile has no delegation step)."""
    if type(req) is not dict or "op" not in req or type(req["op"]) is not str:
        raise Denied("invalid request")
    op = req["op"]
    params = {k: v for k, v in req.items() if k != "op"}
    shapes = {
        "stage": {"body_b64"},
        "review": {"digest"},
        "issue_lease": {"lease_id", "agent_uid", "budget", "expires"},
        "approve": {"nonce", "digest", "destination", "agent_uid", "lease_id", "expires"},
        "revoke": {"lease_id"},
        "delegate": {"nonce", "delegate_uid"},
        "revoke_delegation": {"nonce"},
        "release": {"nonce", "digest", "destination", "lease_id"},
        "effect_release": {"nonce", "digest", "destination", "lease_id"},
        "publish_effect": {"release_id"},
        "halt": set(),
        "state": set(),
    }
    if op not in shapes or set(params) != shapes[op]:
        raise Denied("unreviewed operation or payload shape")
    if op in DELEGATION_OPS and not allow_delegation:
        raise Denied("delegation is disabled in this profile")
    if op == "stage":
        try:
            body = base64.b64decode(params["body_b64"], validate=True)
        except (ValueError, TypeError) as e:
            raise Denied("invalid base64 artifact") from e
        if len(body) > 1024 * 1024:
            raise Denied("oversized artifact")
        return controller.stage(uid, body)
    if op == "review":
        return controller.review(uid, params["digest"])
    if op == "issue_lease":
        return controller.issue_lease(uid, **params)
    if op == "approve":
        return controller.approve(uid, **params)
    if op == "revoke":
        return controller.revoke(uid, **params)
    if op == "delegate":
        return controller.delegate(uid, **params)
    if op == "revoke_delegation":
        return controller.revoke_delegation(uid, **params)
    if op == "release":
        return controller.release(uid, cost=1, **params)
    if op == "effect_release":
        return controller.release(uid, cost=1, record_effect=True, **params)
    if op == "publish_effect":
        if effect_root is None:
            raise Denied("effect root not configured")
        return publish_effect(controller, uid, params["release_id"], effect_root)
    if op == "halt":
        return halt_with_retry(controller, uid)
    return controller.state(uid)


def read_frame(conn, deadline_seconds):
    """One newline-terminated JSON object frame. The deadline covers the whole frame, so a sender that
    trickles bytes cannot hold a worker; a frame that does not start with '{' is refused at its first byte."""
    deadline = time.monotonic() + deadline_seconds
    frame = bytearray()
    while len(frame) <= MAX_REQUEST and not frame.endswith(b"\n"):
        left = deadline - time.monotonic()
        if left <= 0:
            raise Denied("frame deadline exceeded")
        conn.settimeout(left)
        part = conn.recv(min(65536, MAX_REQUEST + 1 - len(frame)))
        if not part:
            break
        frame.extend(part)
        if frame[:1] != b"{":
            raise Denied("invalid frame")
    data = bytes(frame)
    if len(data) > MAX_REQUEST or not data.endswith(b"\n"):
        raise Denied("invalid frame")
    return data


def halt_with_retry(controller, uid, attempts=4):
    """HALT is idempotent, so a busy database is retried rather than reported as final."""
    for attempt in range(attempts):
        try:
            return controller.halt(uid)
        except Denied as e:
            if "persistence unavailable" not in str(e) or attempt == attempts - 1:
                raise


def handle(controller, conn, uid, allow_delegation, effect_root=None):
    """Any failure becomes DENIED: a request must never be able to end the trusted service."""
    try:
        data = read_frame(conn, READ_DEADLINE)
        answer = run_one(controller, uid, json.loads(data), allow_delegation, effect_root=effect_root)
        response = {"ok": True, "result": answer}
    except Exception:  # includes RecursionError from nested JSON and sqlite3.Error
        response = {"ok": False, "error": "DENIED"}
    try:
        conn.settimeout(5)
        conn.sendall((json.dumps(response, sort_keys=True) + "\n").encode())
    except OSError:
        # A caller can disconnect after a transaction commits.
        # Never kill the trusted service or undo that commit;
        # subsequent retry is rejected by the consumed nonce.
        pass


def claim_slot(active, lock, uid, trusted=False):
    with lock:
        limit = MAX_CONNECTIONS if trusted else MAX_CONNECTIONS - RESERVED_FOR_TRUSTED
        if sum(active.values()) >= limit or active.get(uid, 0) >= PER_UID_CONNECTIONS:
            return False
        active[uid] = active.get(uid, 0) + 1
        return True


def release_slot(active, lock, uid):
    with lock:
        active[uid] -= 1
        if not active[uid]:
            del active[uid]


def serve(controller, path, allow_delegation=True, *, effect_root=None):
    """One request per connection, handled on a bounded number of threads. Every connection has a total
    read deadline and each caller UID may hold only PER_UID_CONNECTIONS, so a slow sender cannot stall other
    callers (including HALT). No secret data in error responses."""
    path = Path(path)
    clear_stale_socket(path)
    if not path.parent.is_dir():
        raise Denied("trusted socket directory missing")
    active, lock = {}, threading.Lock()

    def worker(conn, uid):
        try:
            with conn:
                handle(controller, conn, uid, allow_delegation, effect_root)
        finally:
            release_slot(active, lock, uid)

    with socket.socket(socket.AF_UNIX) as sock:
        sock.bind(str(path))
        os.chmod(path, 0o666)  # auth by SO_PEERCRED, not socket file mode
        sock.listen(16)
        try:
            principals = controller.principals
            while True:
                # Nothing a caller does may end the accept loop: transient failures drop that one connection.
                try:
                    conn, _ = sock.accept()
                except OSError:
                    time.sleep(0.05)
                    continue
                try:
                    uid = struct.unpack("iII", conn.getsockopt(socket.SOL_SOCKET,
                          socket.SO_PEERCRED, struct.calcsize("iII")))[1]
                except (OSError, struct.error):
                    conn.close()
                    continue
                trusted = any(principals.allows(uid, role) for role in ("reviewers", "approvers", "admins"))
                if not claim_slot(active, lock, uid, trusted):
                    with conn:
                        try:
                            conn.settimeout(1)
                            conn.sendall(b'{"error": "DENIED", "ok": false}\n')
                        except OSError:
                            pass
                    continue
                try:
                    threading.Thread(target=worker, args=(conn, uid), daemon=True).start()
                except Exception:  # RuntimeError: can't start new thread
                    release_slot(active, lock, uid)
                    conn.close()
        finally:
            path.unlink(missing_ok=True)


def clear_stale_socket(path):
    """Refuse to reuse anything except a dead socket this process owns (left by a killed broker)."""
    if not (path.exists() or path.is_symlink()):
        return
    info = path.lstat()
    if not stat.S_ISSOCK(info.st_mode) or info.st_uid != os.geteuid():
        raise Denied("refusing to reuse/delete an existing socket")
    with socket.socket(socket.AF_UNIX) as probe:
        probe.settimeout(1)
        try:
            probe.connect(str(path))
        except ConnectionRefusedError:
            path.unlink()
            return
        except OSError as e:
            raise Denied("refusing to reuse/delete an existing socket") from e
    raise Denied("a broker is already listening on this socket")


def delegation_rows(db):
    """Rows in the delegations table (0 when the table does not exist yet). A broker started with delegation
    disabled must not inherit a database in which a delegate could still release."""
    import sqlite3
    with contextlib.closing(sqlite3.connect(Path(db).resolve().as_uri() + "?mode=ro", uri=True)) as conn:
        if conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='delegations'").fetchone() is None:
            return 0
        return conn.execute("SELECT COUNT(*) FROM delegations").fetchone()[0]


def args():
    p = argparse.ArgumentParser(allow_abbrev=False)  # no prefix matching: '--allow' must not silently enable delegation
    p.add_argument("--db", type=Path, required=True)
    p.add_argument("--socket", type=Path, required=True)
    for role in ("agents", "reviewers", "approvers", "admins"):
        p.add_argument("--" + role, required=True, help="comma-separated trusted OS UIDs")
    p.add_argument("--bootstrap-cap", type=int, default=None)
    p.add_argument("--effect-root", type=Path, default=None)
    p.add_argument("--allow-delegation", action="store_true",
                   help="enable delegate/revoke_delegation; off by default and outside the R2 claim")
    a = p.parse_args()
    groups = {}
    for role in ("agents", "reviewers", "approvers", "admins"):
        groups[role] = frozenset(map(int, getattr(a, role).split(",")))
    return a, Principals(**groups)


def stored_cap(db):
    import sqlite3
    with contextlib.closing(sqlite3.connect(Path(db).resolve().as_uri() + "?mode=ro", uri=True)) as conn:
        return conn.execute("SELECT global_cap FROM meta WHERE id=1").fetchone()[0]


def main():
    a, principals = args()
    if os.geteuid() in principals.agents:
        raise SystemExit("broker must not run under an untrusted agent UID")
    if os.geteuid() not in principals.admins:
        raise SystemExit("broker must run under an admin UID")
    existing = a.db.exists() or a.db.is_symlink()
    if a.bootstrap_cap is not None and not existing:
        c = Controller.bootstrap(a.db, principals, a.bootstrap_cap)
    else:
        # A restart (for example `docker start`) reopens the existing database; --bootstrap-cap must still agree with it.
        # Open it read-write FIRST: that rolls back the journal a killed broker may have left, which a read-only open cannot.
        c = Controller(a.db, principals)
        if a.bootstrap_cap is not None and stored_cap(a.db) != a.bootstrap_cap:
            raise SystemExit("--bootstrap-cap disagrees with the existing database")
    if not a.allow_delegation and delegation_rows(a.db):
        raise SystemExit("delegation disabled but the database already holds delegation rows; refusing to serve")
    serve(c, a.socket, allow_delegation=a.allow_delegation, effect_root=a.effect_root)


if __name__ == "__main__":
    main()
