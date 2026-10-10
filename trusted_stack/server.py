"""Unix peer-credential broker for trusted_stack.Controller.

The broker alone owns the 0600 database and derives caller UID from
SO_PEERCRED; never pass caller-supplied identity in a request. This is a
reference interface, not a network-facing or production authorization server.
"""
import argparse
import base64
import json
import os
import socket
import stat
import struct
from pathlib import Path
from .controller import Controller, Denied, Principals
from .publisher import publish_effect

MAX_REQUEST = 1500000


def run_one(controller, uid, req, *, effect_root=None):
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
        "release": {"nonce", "digest", "destination", "lease_id"},
        "effect_release": {"nonce", "digest", "destination", "lease_id"},
        "publish_effect": {"release_id"},
        "halt": set(),
        "state": set(),
    }
    if op not in shapes or set(params) != shapes[op]:
        raise Denied("unreviewed operation or payload shape")
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
    if op == "release":
        return controller.release(uid, cost=1, **params)
    if op == "effect_release":
        return controller.release(uid, cost=1, record_effect=True, **params)
    if op == "publish_effect":
        if effect_root is None:
            raise Denied("effect root not configured")
        return publish_effect(controller, uid, params["release_id"], effect_root)
    if op == "halt":
        return controller.halt(uid)
    return controller.state(uid)


def serve(controller, path, *, effect_root=None):
    """One request per connection. No secret data in error responses."""
    path = Path(path)
    if path.exists() or path.is_symlink():
        raise Denied("refusing to reuse/delete an existing socket")
    if not path.parent.is_dir():
        raise Denied("trusted socket directory missing")
    with socket.socket(socket.AF_UNIX) as sock:
        sock.bind(str(path))
        os.chmod(path, 0o666)  # auth by SO_PEERCRED, not socket file mode
        sock.listen(16)
        try:
            while True:
                conn, _ = sock.accept()
                with conn:
                    uid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET,
                          socket.SO_PEERCRED, struct.calcsize("3i")))[1]
                    try:
                        conn.settimeout(5)
                        frame = bytearray()
                        while len(frame) <= MAX_REQUEST and not frame.endswith(b"\n"):
                            part = conn.recv(min(65536, MAX_REQUEST + 1 - len(frame)))
                            if not part:
                                break
                            frame.extend(part)
                        data = bytes(frame)
                        if len(data) > MAX_REQUEST or not data.endswith(b"\n"):
                            raise Denied("invalid frame")
                        answer = run_one(controller, uid, json.loads(data), effect_root=effect_root)
                        response = {"ok": True, "result": answer}
                    except (Denied, ValueError, TypeError, KeyError, json.JSONDecodeError, OSError):
                        response = {"ok": False, "error": "DENIED"}
                    try:
                        conn.sendall((json.dumps(response, sort_keys=True) + "\n").encode())
                    except OSError:
                        # A caller can disconnect after a transaction commits.
                        # Never kill the trusted service or undo that commit;
                        # subsequent retry is rejected by the consumed nonce.
                        pass
        finally:
            path.unlink(missing_ok=True)


def args():
    p = argparse.ArgumentParser()
    p.add_argument("--db", type=Path, required=True)
    p.add_argument("--socket", type=Path, required=True)
    for role in ("agents", "reviewers", "approvers", "admins"):
        p.add_argument("--" + role, required=True, help="comma-separated trusted OS UIDs")
    p.add_argument("--bootstrap-cap", type=int, default=None)
    p.add_argument("--effect-root", type=Path, default=None)
    a = p.parse_args()
    groups = {}
    for role in ("agents", "reviewers", "approvers", "admins"):
        groups[role] = frozenset(map(int, getattr(a, role).split(",")))
    return a, Principals(**groups)


if __name__ == "__main__":
    a, principals = args()
    if a.bootstrap_cap is not None:
        c = Controller.bootstrap(a.db, principals, a.bootstrap_cap)
    else:
        c = Controller(a.db, principals)
    if os.geteuid() in principals.agents:
        raise SystemExit("broker must not run under an untrusted agent UID")
    serve(c, a.socket, effect_root=a.effect_root)
