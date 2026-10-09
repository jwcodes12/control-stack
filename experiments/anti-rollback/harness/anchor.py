#!/usr/bin/env python3
"""Anchor service: the stand-in for a TPM NV monotonic counter or a transparency-log head (Python 3.9 compatible).

Runs as its own numeric UID with a private 0700 directory. State: (version, digest). Durable: every change is written to
a temporary file, fsynced, renamed over `state.json`, and the directory fsynced; every accepted increment is also
appended (and fsynced) to the append-only `anchor.log`, the anchor's OWN record used by the independent reconciliation.

Unix-socket ops (caller identity from SO_PEERCRED, never from the request):
  {"op":"read"}                          -> {"version": v, "digest": d}       (gate and auditor UIDs only)
  {"op":"increment","to":v,"digest":d}   -> accepted only from the gate UID and only if v == version + 1
                                            (strictly monotone, no gaps); anything else is refused
There is no decrement, reset or set operation.
"""
import argparse
import json
import os
import socket
import struct
import sys
import threading

GENESIS = "0" * 64


class Refused(Exception):
    pass


class AnchorStore:
    def __init__(self, d):
        self.d = str(d)
        self.state_path = os.path.join(self.d, "state.json")
        self.log_path = os.path.join(self.d, "anchor.log")
        self.lock = threading.Lock()
        if os.path.exists(self.state_path):
            with open(self.state_path) as f:
                s = json.load(f)
            self.version, self.digest = int(s["version"]), s["digest"]
        else:
            self.version, self.digest = 0, GENESIS
            self._persist()

    def _persist(self):
        tmp = self.state_path + ".tmp"
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        try:
            os.write(fd, json.dumps({"version": self.version, "digest": self.digest}).encode())
            os.fsync(fd)
        finally:
            os.close(fd)
        os.rename(tmp, self.state_path)
        dfd = os.open(self.d, os.O_RDONLY)
        try:
            os.fsync(dfd)
        finally:
            os.close(dfd)

    def read(self):
        with self.lock:
            return {"version": self.version, "digest": self.digest}

    def increment(self, to, digest):
        with self.lock:
            if type(to) is not int or to != self.version + 1:
                raise Refused("non-monotone increment refused (have %d, asked %r)" % (self.version, to))
            if type(digest) is not str or len(digest) != 64:
                raise Refused("bad digest")
            fd = os.open(self.log_path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
            try:
                os.write(fd, (json.dumps({"version": to, "digest": digest}) + "\n").encode())
                os.fsync(fd)
            finally:
                os.close(fd)
            self.version, self.digest = to, digest
            self._persist()
            return {"version": self.version, "digest": self.digest}


def peer_uid(conn):
    return struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))[1]


def serve(store, sock_path, gate_uid, readers):
    srv = socket.socket(socket.AF_UNIX)
    if os.path.exists(sock_path):
        os.unlink(sock_path)
    srv.bind(sock_path)
    os.chmod(sock_path, 0o666)  # authentication is SO_PEERCRED
    srv.listen(16)
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
                if req.get("op") == "read" and set(req) == {"op"} and (uid == gate_uid or uid in readers):
                    reply = {"ok": True, "result": store.read()}
                elif req.get("op") == "increment" and set(req) == {"op", "to", "digest"} and uid == gate_uid:
                    reply = {"ok": True, "result": store.increment(req["to"], req["digest"])}
                else:
                    reply = {"ok": False, "error": "refused"}
            except Refused as e:
                reply = {"ok": False, "error": str(e)}
            except (ValueError, OSError) as e:
                reply = {"ok": False, "error": "malformed: " + type(e).__name__}
            try:
                conn.sendall((json.dumps(reply) + "\n").encode())
            except OSError:
                pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--socket", required=True)
    ap.add_argument("--gate-uid", type=int, required=True)
    ap.add_argument("--reader-uid", type=int, action="append", default=[])
    a = ap.parse_args()
    store = AnchorStore(a.dir)
    sys.stdout.write("READY\n")
    sys.stdout.flush()
    serve(store, a.socket, a.gate_uid, set(a.reader_uid))


if __name__ == "__main__":
    main()
