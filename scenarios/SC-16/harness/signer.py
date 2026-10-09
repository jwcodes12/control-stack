#!/usr/bin/env python3
"""SC-16 deploy admission: a signing principal, reviewer or approver (prereg/SC16-DEPLOY-ADMISSION.md).

Each principal generates its own Ed25519 key with openssl in its private directory (mode 0700) at start and prints
the public key path; it alone uses the private key. Every decision is appended to its own fsync'd log, followed by a
{"commit": seq, "t": ns} line.

reviewer  {"op": "review", "digest", "target"}: fetch the bytes BY DIGEST from the registry, check SHA-256, refuse if
          the content's stager is this reviewer (distinctness; `--no-distinct-check` is the NEGATIVE_CONTROL), apply
          the benign policy (no FORBIDDEN marker), sign "sc16-review|<digest>|<target>".
          {"op": "stage", "data_b64"}: put content into the registry AS this principal (used only by the
          self-review control).
approver  {"op": "approve", "digest", "target", "review_sig", "tag"}: verify the reviewer's signature for exactly
          (digest, target), mint a fresh one-use nonce, sign "sc16-approval|<nonce>|<digest>|<target>|<tag>".
Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import base64
import hashlib
import json
import os
import secrets
import socket
import subprocess
import sys
import tempfile
import threading
import time


def rpc(path, obj, timeout=5.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        return json.loads(f.readline())
    finally:
        s.close()


def review_msg(digest, target):
    return ("sc16-review|%s|%s" % (digest, target)).encode()


def approval_msg(nonce, digest, target, tag):
    return ("sc16-approval|%s|%s|%s|%s" % (nonce, digest, target, tag or "")).encode()


def sign(openssl, key, msg, tmpdir):
    with tempfile.NamedTemporaryFile(dir=tmpdir, delete=False) as fh:
        fh.write(msg)
    try:
        r = subprocess.run([openssl, "pkeyutl", "-sign", "-inkey", key, "-rawin", "-in", fh.name],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        return r.stdout.hex()
    finally:
        os.unlink(fh.name)


def verify(openssl, pub, msg, sig_hex, tmpdir):
    try:
        sig = bytes.fromhex(sig_hex or "")
    except ValueError:
        return False
    with tempfile.NamedTemporaryFile(dir=tmpdir, delete=False) as m, \
            tempfile.NamedTemporaryFile(dir=tmpdir, delete=False) as s:
        m.write(msg)
        s.write(sig)
    try:
        r = subprocess.run([openssl, "pkeyutl", "-verify", "-pubin", "-inkey", pub, "-rawin", "-in", m.name,
                            "-sigfile", s.name], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return r.returncode == 0
    finally:
        os.unlink(m.name)
        os.unlink(s.name)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--role", choices=["reviewer", "approver"], required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--dir", required=True, help="private directory (key, temp files)")
    ap.add_argument("--sock", required=True)
    ap.add_argument("--registry", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--reviewer-pub", help="approver: the reviewer's public key")
    ap.add_argument("--openssl", default="/usr/bin/openssl")
    ap.add_argument("--no-distinct-check", action="store_true", help="NEGATIVE_CONTROL (reviewer)")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    os.makedirs(a.dir, mode=0o700, exist_ok=True)
    key, pub = os.path.join(a.dir, "key.pem"), os.path.join(a.dir, "pub.pem")
    subprocess.run([a.openssl, "genpkey", "-algorithm", "ed25519", "-out", key], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    os.chmod(key, 0o600)
    subprocess.run([a.openssl, "pkey", "-in", key, "-pubout", "-out", pub], check=True)
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]

    def record(rec):
        with lock:
            rec["seq"] = seq[0]
            seq[0] += 1
            os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
            os.fsync(fd)
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": time.monotonic_ns()}) + "\n").encode())
            return rec

    def handle(m):
        op = m.get("op")
        if a.role == "reviewer" and op == "stage":
            return rpc(a.registry, {"op": "put", "data_b64": m["data_b64"]})
        if a.role == "reviewer" and op == "review":
            d, t = str(m.get("digest")), str(m.get("target"))
            got = rpc(a.registry, {"op": "get", "digest": d})
            if not got.get("ok"):
                return {"ok": False, "error": "no such digest"}
            data = base64.b64decode(got["data_b64"])
            base = {"digest": d, "target": t, "stager": got["stager"], "reviewer": a.name,
                    "content_sha": hashlib.sha256(data).hexdigest()}
            if base["content_sha"] != d:
                return {"ok": False, "error": "store returned content with another digest"}
            if not a.no_distinct_check and got["stager"] == a.name:
                record(dict(base, verdict="refused", why="reviewer is the stager"))
                return {"ok": False, "error": "reviewer is the stager"}
            if b"FORBIDDEN" in data:
                record(dict(base, verdict="fail", why="policy"))
                return {"ok": False, "error": "review failed"}
            sig = sign(a.openssl, key, review_msg(d, t), a.dir)
            record(dict(base, verdict="pass", sig=sig))
            return {"ok": True, "sig": sig, "reviewer": a.name}
        if a.role == "approver" and op == "approve":
            d, t, tag = str(m.get("digest")), str(m.get("target")), m.get("tag")
            if not verify(a.openssl, a.reviewer_pub, review_msg(d, t), m.get("review_sig"), a.dir):
                record({"digest": d, "target": t, "verdict": "refused", "why": "no valid review signature"})
                return {"ok": False, "error": "no valid review signature for this digest and target"}
            nonce = secrets.token_hex(16)
            sig = sign(a.openssl, key, approval_msg(nonce, d, t, tag), a.dir)
            appr = {"nonce": nonce, "digest": d, "target": t, "tag": tag, "approver": a.name, "sig": sig}
            record(dict(appr, verdict="approved"))
            return {"ok": True, "approval": appr}
        return {"ok": False, "error": "unknown op for %s" % a.role}

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                try:
                    r = handle(json.loads(line))
                except Exception as e:
                    r = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(64)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "pub": pub, "name": a.name}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
