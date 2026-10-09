#!/usr/bin/env python3
"""SC-11 build step (prereg/SC10-POLICY-STORE.md).

{"op": "build", "path_env": "..."} on build.sock. Deployed configuration (`pinnedPath`): the toolchain is the file at
the PINNED absolute path; the builder hashes the bytes it read from it and refuses unless they have the pinned digest;
it then runs exactly those bytes (a copy in its own 0700 directory, named by digest) with the system interpreter. The
PATH the caller supplies is ignored. NEGATIVE_CONTROL: --path-resolve resolves "toolchain" through the caller's PATH
and runs whatever it finds, unchecked (`path_toolchain_breaks`). Every build's toolchain writes its own SHA-256 into
the build output (an independent record of what actually ran). Self-contained.
"""
import argparse
import hashlib
import json
import os
import shutil
import socket
import subprocess
import sys
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--pinned", required=True)
    ap.add_argument("--pinned-digest", required=True)
    ap.add_argument("--pin-dir", required=True)
    ap.add_argument("--outputs", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--path-resolve", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    os.makedirs(a.pin_dir, mode=0o700, exist_ok=True)
    os.makedirs(a.outputs, mode=0o700, exist_ok=True)
    lock, n = threading.Lock(), [0]
    logf = open(a.log, "a", buffering=1)

    def build(m):
        with lock:
            n[0] += 1
            out = os.path.join(a.outputs, "build-%03d.json" % n[0])
            rec = {"build": n[0], "output": out, "path_resolve": a.path_resolve}
            if a.path_resolve:
                tool = shutil.which("toolchain", path=m.get("path_env", ""))
                if tool is None:
                    rec.update(ok=False, why="toolchain not found on PATH")
                    logf.write(json.dumps(rec) + "\n")
                    return rec
                run_path = tool
                rec["resolved"] = tool
            else:
                with open(a.pinned, "rb") as fh:
                    data = fh.read()
                d = hashlib.sha256(data).hexdigest()
                rec["checked_digest"] = d
                if d != a.pinned_digest:
                    rec.update(ok=False, why="toolchain digest mismatch")
                    logf.write(json.dumps(rec) + "\n")
                    return rec
                run_path = os.path.join(a.pin_dir, d + ".py")
                if not os.path.exists(run_path):
                    with open(run_path + ".tmp", "wb") as fh:
                        fh.write(data)
                    os.chmod(run_path + ".tmp", 0o400)
                    os.rename(run_path + ".tmp", run_path)
            r = subprocess.run([sys.executable, "-I", "-S", "-B", run_path, out], stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10,
                               env={"PATH": "/usr/bin:/bin"})
            rec.update(ok=r.returncode == 0, rc=r.returncode, t=time.monotonic_ns())
            logf.write(json.dumps(rec) + "\n")
            return rec

    def serve(conn):
        f = conn.makefile("rwb")
        try:
            for line in f:
                m = json.loads(line)
                try:
                    r = build(m) if m.get("op") == "build" else {"ok": False, "why": "unknown op"}
                except Exception as e:
                    r = {"ok": False, "why": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
                f.flush()
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(16)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "path_resolve": a.path_resolve}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
