#!/usr/bin/env python3
"""Live local SO_PEERCRED identity-spoof negative test. Requires root on Linux.

This starts an actual Unix socket broker with a private SQLite state store,
then makes agent, reviewer, approver, admin and forged requests from different
host process UIDs. It invokes NO external deploy, exec or egress adapter.
"""
import base64
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from trusted_stack.client import request

AGENT, REVIEWER, APPROVER, OTHER = 23501, 23502, 23503, 23504


def by_uid(uid, socketpath, data):
    program = (
        "import json,sys; from trusted_stack.client import request; "
        "print(json.dumps(request(sys.argv[1],json.loads(sys.argv[2]))))"
    )
    process = subprocess.run([sys.executable, "-c", program, str(socketpath), json.dumps(data)],
                             cwd=Path(__file__).resolve().parents[1], capture_output=True,
                             text=True, check=True, preexec_fn=(lambda: os.setuid(uid)))
    return json.loads(process.stdout)


def main():
    if os.geteuid() != 0:
        raise SystemExit("root required to simulate separate real Linux UIDs")
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        root.chmod(0o755)
        state = root / "private"
        state.mkdir(mode=0o700)
        sockpath = root / "trusted.sock"
        cmd = [sys.executable, "-m", "trusted_stack.server",
               "--db", str(state / "state.sqlite"),
               "--socket", str(sockpath),
               "--agents", str(AGENT),
               "--reviewers", str(REVIEWER),
               "--approvers", str(APPROVER),
               "--admins", "0",
               "--bootstrap-cap", "2"]
        proc = subprocess.Popen(cmd, cwd=Path(__file__).resolve().parents[1],
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        try:
            for _ in range(100):
                if sockpath.exists():
                    break
                if proc.poll() is not None:
                    raise RuntimeError("broker exited during start: " + str(proc.stderr.read()))
                time.sleep(.04)
            else:
                raise RuntimeError("broker socket not ready")
            content = b"test-only approved artifact"
            digest = hashlib.sha256(content).hexdigest()
            def call(uid, data, permitted):
                reply = by_uid(uid, sockpath, data)
                assert reply["ok"] is permitted, (uid, data, reply)
                return reply
            call(AGENT, {"op": "stage", "body_b64": base64.b64encode(content).decode()}, True)
            call(AGENT, {"op": "review", "digest": digest}, False)
            call(REVIEWER, {"op": "review", "digest": digest}, True)
            call(0, {"op": "issue_lease", "lease_id": "lease1", "agent_uid": AGENT,
                     "budget": 1, "expires": int(time.time()) + 500}, True)
            call(AGENT, {"op": "approve", "nonce": "n1", "digest": digest,
                         "destination": "staging/item", "agent_uid": AGENT,
                         "lease_id": "lease1", "expires": int(time.time()) + 400}, False)
            call(APPROVER, {"op": "approve", "nonce": "n1", "digest": digest,
                            "destination": "staging/item", "agent_uid": AGENT,
                            "lease_id": "lease1", "expires": int(time.time()) + 400}, True)
            release = {"op": "release", "nonce": "n1", "digest": digest,
                       "destination": "staging/item", "lease_id": "lease1"}
            call(OTHER, release, False)
            call(AGENT, {**release, "uid": 0}, False)
            call(AGENT, release, True)
            call(AGENT, release, False)
            call(0, {"op": "halt"}, True)
            call(AGENT, {"op": "stage", "body_b64": base64.b64encode(b"x").decode()}, False)
            assert call(0, {"op": "state"}, True)["result"] == {
                "global_cap": 2, "halted": True, "spent": 1, "releases": 1}
            print("PASS: 13 real Unix peer-credential broker checks, 1 atomic release record; no external effects")
        finally:
            proc.terminate()
            try:
                proc.communicate(timeout=4)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate(timeout=4)


if __name__ == "__main__":
    main()
