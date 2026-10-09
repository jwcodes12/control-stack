#!/usr/bin/env python3
"""SC-16 deploy admission: the admission controller (prereg/SC16-DEPLOY-ADMISSION.md).

Single-threaded; the only writer of the disposable target directories (<targets>/staging, <targets>/prod).
agent.sock  {"op": "deploy", "approval": {nonce, digest, target, tag, approver, sig}, "review_sig", "target"}
admin.sock  {"op": "halt"}, {"op": "status"}
Deployed configuration (model `full`), in order:
  halted -> refuse; the approval's Ed25519 signature verifies under the approver's public key; its nonce is unused
  (one-use, kept in an fsync'd file); the requested target equals the approval's target; a reviewer signature
  verifies for exactly (approval digest, approval target); the bytes are fetched BY DIGEST from the CAS and their
  SHA-256 must equal the approved digest (`verify`); then the file is written (tmp + fsync + rename + dir fsync), a
  deploy record is fsync'd, and the nonce is marked used.
NEGATIVE_CONTROL flags: --by-tag (deploy whatever the approval's mutable tag points to now, no digest check:
`toctou_slot_breaks`), --no-target-binding (`no_target_binding_breaks`), --no-nonce (`no_nonce_redeploys`).
Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import base64
import hashlib
import json
import os
import selectors
import socket
import subprocess
import sys
import tempfile
import time

TARGETS = ("staging", "prod")


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
    ap.add_argument("--dir", required=True, help="private dir: sockets, temp files")
    ap.add_argument("--targets", required=True)
    ap.add_argument("--registry", required=True)
    ap.add_argument("--reviewer-pub", required=True)
    ap.add_argument("--approver-pub", required=True)
    ap.add_argument("--deploy-log", required=True)
    ap.add_argument("--used", required=True)
    ap.add_argument("--openssl", default="/usr/bin/openssl")
    ap.add_argument("--by-tag", action="store_true")
    ap.add_argument("--no-target-binding", action="store_true")
    ap.add_argument("--no-nonce", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    config = {"by_tag": a.by_tag, "no_target_binding": a.no_target_binding, "no_nonce": a.no_nonce}
    t_end = time.monotonic() + a.lifetime
    for t in TARGETS:
        os.makedirs(os.path.join(a.targets, t), mode=0o700, exist_ok=True)
    dfd = os.open(a.deploy_log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    ufd = os.open(a.used, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    used, halted, seq = set(), [False], [0]

    def deploy(m):
        if halted[0]:
            return {"ok": False, "error": "halted"}
        ap_, target = m.get("approval") or {}, m.get("target")
        if target not in TARGETS:
            return {"ok": False, "error": "unknown target"}
        msg = ("sc16-approval|%s|%s|%s|%s" % (ap_.get("nonce"), ap_.get("digest"), ap_.get("target"),
                                             ap_.get("tag") or "")).encode()
        if not verify(a.openssl, a.approver_pub, msg, ap_.get("sig"), a.dir):
            return {"ok": False, "error": "bad approval signature"}
        if not a.no_nonce and ap_["nonce"] in used:
            return {"ok": False, "error": "approval already used"}
        if not a.no_target_binding and target != ap_["target"]:
            return {"ok": False, "error": "target differs from the approved target"}
        rmsg = ("sc16-review|%s|%s" % (ap_["digest"], ap_["target"])).encode()
        if not verify(a.openssl, a.reviewer_pub, rmsg, m.get("review_sig"), a.dir):
            return {"ok": False, "error": "no valid review signature"}
        if a.by_tag:
            cur = rpc(a.registry, {"op": "tag_get", "tag": ap_.get("tag")})
            if not cur.get("ok"):
                return {"ok": False, "error": "no such tag"}
            got = rpc(a.registry, {"op": "get", "digest": cur["digest"]})
            data = base64.b64decode(got["data_b64"])
        else:
            got = rpc(a.registry, {"op": "get", "digest": ap_["digest"]})
            if not got.get("ok"):
                return {"ok": False, "error": "approved digest not in store"}
            data = base64.b64decode(got["data_b64"])
            if hashlib.sha256(data).hexdigest() != ap_["digest"]:
                return {"ok": False, "error": "content does not hash to the approved digest"}
        name = "%04d-%s.bin" % (seq[0], ap_["nonce"][:8])
        tdir = os.path.join(a.targets, target)
        tmp = os.path.join(tdir, "." + name + ".tmp")
        with open(tmp, "wb") as fh:
            fh.write(data)
            fh.flush()
            os.fsync(fh.fileno())
        os.rename(tmp, os.path.join(tdir, name))
        dirfd = os.open(tdir, os.O_RDONLY)
        os.fsync(dirfd)
        os.close(dirfd)
        rec = {"seq": seq[0], "file": "%s/%s" % (target, name), "nonce": ap_["nonce"], "target": target,
               "approved_digest": ap_["digest"], "sha": hashlib.sha256(data).hexdigest(), "config": config}
        os.write(dfd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        os.fsync(dfd)
        t = time.monotonic_ns()
        os.write(dfd, (json.dumps({"commit": seq[0], "t": t}) + "\n").encode())
        used.add(ap_["nonce"])
        os.write(ufd, (ap_["nonce"] + "\n").encode())
        os.fsync(ufd)
        seq[0] += 1
        return {"ok": True, "file": rec["file"], "sha": rec["sha"], "t": t}

    sel = selectors.DefaultSelector()
    for role in ("agent", "admin"):
        p = os.path.join(a.dir, role + ".sock")
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(p)
        os.chmod(p, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", role))
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.2):
            kind, role = key.data
            if kind == "listen":
                try:
                    conn, _ = key.fileobj.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                conn.setblocking(True)
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, ("conn", role))
                continue
            conn = key.fileobj
            try:
                chunk = conn.recv(65536)
            except OSError:
                chunk = b""
            if not chunk:
                sel.unregister(conn)
                conn.close()
                bufs.pop(conn, None)
                continue
            bufs[conn] += chunk
            while b"\n" in bufs[conn]:
                line, bufs[conn] = bufs[conn].split(b"\n", 1)
                try:
                    m = json.loads(line)
                    if role == "agent" and m.get("op") == "deploy":
                        reply = deploy(m)
                    elif role == "admin" and m.get("op") == "halt":
                        halted[0] = True
                        reply = {"ok": True, "t": time.monotonic_ns()}
                    elif role == "admin":
                        reply = {"ok": True, "halted": halted[0], "deployed": seq[0], "config": config}
                    else:
                        reply = {"ok": False, "error": "unknown op"}
                except Exception as e:
                    reply = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
