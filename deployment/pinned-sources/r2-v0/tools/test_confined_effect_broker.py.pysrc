#!/usr/bin/env python3
"""True Linux cross-UID broker + confined delegated agent + real file effect.

Requires root only for disposable UID changes, not to bypass permissions.
This is host-specific evidence for one pre-opened broker socket and one
trusted local file receiver. No general OS/network guarantee is inferred.
"""
import base64
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from trusted_stack.controller import Controller, Principals
from trusted_stack.outbox_receiver import deliver_record
from trusted_stack.client import request

AGENT_OWNER = 23701
AGENT_DELEGATE = 23702
REVIEWER = 23703
APPROVER = 23704


def drop_identity(uid):
    os.setgroups([])
    os.setgid(uid)
    os.setuid(uid)


def by_uid(uid, cwd, socketpath, data):
    script = ("import json,sys;from trusted_stack.client import request;"
              "print(json.dumps(request(sys.argv[1],json.loads(sys.argv[2]))))")
    proc = subprocess.run([sys.executable, "-c", script, str(socketpath),
                           json.dumps(data)], cwd=cwd, capture_output=True,
                          text=True, preexec_fn=lambda: drop_identity(uid), timeout=25)
    if proc.returncode:
        raise AssertionError(proc.stderr)
    return json.loads(proc.stdout)


def run():
    if os.geteuid() != 0 or not sys.platform.startswith("linux"):
        raise SystemExit("root on disposable Linux host required")
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        root.chmod(0o755)
        childdir = root / "worker"
        childdir.mkdir(mode=0o755)
        shutil.copytree(Path(__file__).resolve().parents[1] / "trusted_stack",
                        childdir / "trusted_stack")
        dbdir = root / "private"
        dbdir.mkdir(mode=0o700)
        outdir = root / "published"
        outdir.mkdir(mode=0o700)
        forbidden = root / "forbidden-effect"
        socketpath = root / "trusted.sock"
        dbfile = dbdir / "state.db"
        cmd = [sys.executable, "-m", "trusted_stack.server",
               "--db", str(dbfile), "--socket", str(socketpath),
               "--agents", f"{AGENT_OWNER},{AGENT_DELEGATE}",
               "--reviewers", str(REVIEWER), "--approvers", str(APPROVER),
               "--admins", "0", "--bootstrap-cap", "1"]
        server = subprocess.Popen(cmd, cwd=Path(__file__).resolve().parents[1],
                                  stdout=subprocess.DEVNULL,
                                  stderr=subprocess.PIPE, text=True)
        try:
            for _ in range(150):
                if socketpath.exists():
                    break
                if server.poll() is not None:
                    raise AssertionError("server died: " + server.stderr.read())
                time.sleep(.04)
            else:
                raise AssertionError("broker socket missing")
            body = b"reviewed-frozen-delegated-agent-effect"
            digest = hashlib.sha256(body).hexdigest()
            def call(uid, data, allowed=True):
                res = by_uid(uid, childdir, socketpath, data)
                assert res["ok"] is allowed, (uid, data, res)
                return res
            call(AGENT_OWNER, {"op": "stage",
                "body_b64": base64.b64encode(body).decode()})
            call(REVIEWER, {"op": "review", "digest": digest})
            expiry = int(time.time()) + 300
            call(0, {"op": "issue_lease", "lease_id": "lease-a",
                     "agent_uid": AGENT_OWNER, "budget": 1, "expires": expiry})
            call(APPROVER, {"op": "approve", "nonce": "nonce-a",
                            "digest": digest, "destination": "trusted/local-effect",
                            "agent_uid": AGENT_OWNER, "lease_id": "lease-a",
                            "expires": expiry})
            call(AGENT_OWNER, {"op": "delegate", "nonce": "nonce-a",
                                "delegate_uid": AGENT_DELEGATE})
            req = {"op": "effect_release", "nonce": "nonce-a",
                   "digest": digest, "destination": "trusted/local-effect",
                   "lease_id": "lease-a"}
            call(AGENT_OWNER, req, allowed=False)
            source = (
                "import json,os,socket,errno\n"
                f"forbidden={str(forbidden)!r}\n"
                f"request={req!r}\n"
                "try: open(forbidden,'wb').write(b'wrong')\n"
                "except OSError as e: assert e.errno in (errno.EACCES,errno.EPERM)\n"
                "else: raise RuntimeError('unauthorized filesystem effect')\n"
                "try: socket.socket(socket.AF_INET,socket.SOCK_STREAM)\n"
                "except OSError as e: assert e.errno in (errno.EACCES,errno.EPERM)\n"
                "else: raise RuntimeError('unauthorized network socket')\n"
                "os.write(3,(json.dumps(request)+'\\n').encode())\n"
                "answer=json.loads(os.read(3,65536))\n"
                "assert answer['ok'] is True, answer\n"
                "assert answer['result'] == 1, answer\n"
            )
            scriptpath = childdir / "source.py"
            scriptpath.write_text(source)
            scriptpath.chmod(0o644)
            proc = subprocess.run(
                [sys.executable, "-m", "trusted_stack.agent_confinement",
                 "--script", str(scriptpath), "--broker-socket", str(socketpath),
                 "--broker-uid", "0"],
                preexec_fn=lambda: drop_identity(AGENT_DELEGATE),
                cwd=childdir, capture_output=True, text=True, timeout=30)
            assert proc.returncode == 0, (proc.returncode, proc.stderr)
            assert not forbidden.exists(), "forbidden file created"
            state = call(0, {"op": "state"})["result"]
            assert state["spent"] == 1 and state["releases"] == 1, state
            roles = Principals(frozenset({AGENT_OWNER, AGENT_DELEGATE}),
                               frozenset({REVIEWER}), frozenset({APPROVER}),
                               frozenset({0}))
            controller = Controller(dbfile, roles)
            assert deliver_record(controller, 1, outdir) == "1.body"
            assert (outdir / "1.body").read_bytes() == body
            call(AGENT_DELEGATE, req, allowed=False)
            call(0, {"op": "halt"})
            assert (outdir / "1.body").read_bytes() == body
            print("PASS: real kernel-confined delegate, SO_PEERCRED, one shared "
                  "budget, exactly-one trusted file effect, replay/HALT negatives")
        finally:
            server.terminate()
            try:
                server.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                server.kill()
                server.communicate(timeout=5)


if __name__ == "__main__":
    run()
