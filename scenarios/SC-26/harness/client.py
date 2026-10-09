"""One-request Unix-socket JSON client. This is the ONLY harness module copied to the untrusted import directory.

Identity is never sent: each server derives the caller from SO_PEERCRED."""
import json
import socket


def call(path, req, timeout=15):
    with socket.socket(socket.AF_UNIX) as s:
        s.settimeout(timeout)
        s.connect(str(path))
        s.sendall((json.dumps(req, sort_keys=True) + "\n").encode())
        buf = bytearray()
        while not buf.endswith(b"\n"):
            part = s.recv(65536)
            if not part:
                break
            buf.extend(part)
    if not buf:
        raise ConnectionError("no reply (server closed the connection)")
    return json.loads(bytes(buf))
