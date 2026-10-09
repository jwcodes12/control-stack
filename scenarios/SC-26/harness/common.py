"""Server-side helpers shared by bank.py and txgate.py (trusted code; never imported by untrusted children)."""
import json
import os
import socket
import socketserver
import struct
from pathlib import Path

MAX_FRAME = 65536


class Refused(Exception):
    pass


def peer_uid(conn):
    pid, uid, gid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))
    return uid


def nat(x):
    """a natural number as the Lean model's ℕ (bool is not accepted)"""
    if type(x) is not int or x < 0 or x >= 2 ** 62:
        raise Refused("not a natural number")
    return x


def tx_of(d):
    if type(d) is not dict or set(d) != {"dest", "amount", "memo"}:
        raise Refused("bad payload shape")
    return (nat(d["dest"]), nat(d["amount"]), nat(d["memo"]))


def read_frame(conn):
    conn.settimeout(10)
    buf = bytearray()
    while len(buf) <= MAX_FRAME and not buf.endswith(b"\n"):
        part = conn.recv(MAX_FRAME + 1 - len(buf))
        if not part:
            break
        buf.extend(part)
    if len(buf) > MAX_FRAME or not buf.endswith(b"\n"):
        raise Refused("bad frame")
    req = json.loads(bytes(buf))
    if type(req) is not dict or type(req.get("op")) is not str:
        raise Refused("bad request")
    return req


def shape(req, keys):
    if set(req) != set(keys) | {"op"}:
        raise Refused("unexpected request fields")


class Server(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    allow_reuse_address = False


def make_handler(dispatch):
    class H(socketserver.BaseRequestHandler):
        def handle(self):
            uid = peer_uid(self.request)
            try:
                req = read_frame(self.request)
                reply = {"ok": True, "result": dispatch(uid, req)}
            except Refused as e:
                reply = {"ok": False, "error": str(e)}
            except (ValueError, TypeError, KeyError, json.JSONDecodeError) as e:
                reply = {"ok": False, "error": "malformed: " + type(e).__name__}
            try:
                self.request.sendall((json.dumps(reply, sort_keys=True) + "\n").encode())
            except OSError:
                pass
    return H


def make_server(path, dispatch):
    path = Path(path)
    if path.is_symlink():
        raise SystemExit("refusing symlinked socket path")
    if path.exists():
        path.unlink()  # stale socket from a crashed run, in a directory only this UID can write
    srv = Server(str(path), make_handler(dispatch))
    os.chmod(path, 0o666)  # authentication is SO_PEERCRED, not the file mode
    return srv


def serve(path, dispatch):
    make_server(path, dispatch).serve_forever()
