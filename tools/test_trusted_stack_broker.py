#!/usr/bin/env python3
"""Live local SO_PEERCRED identity-spoof negative test. Requires root on Linux.

This starts an actual Unix socket broker with a private SQLite state store,
then makes agent, reviewer, approver, admin and forged requests from different
host process UIDs. It makes exactly one broker-owned file publication; no exec or egress.
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
from trusted_stack.client import request

AGENT, REVIEWER, APPROVER, OTHER = 23501, 23502, 23503, 23504


def by_uid(uid, socketpath, data):
    program = (
        "import json,sys; from trusted_stack.client import request; "
        "print(json.dumps(request(sys.argv[1],json.loads(sys.argv[2]))))"
    )
    process = subprocess.run([sys.executable, "-c", program, str(socketpath), json.dumps(data)],
                             cwd=socketpath.parent / "agent-import", capture_output=True,
                             text=True, preexec_fn=(lambda: os.setuid(uid)))
    if process.returncode:
        raise RuntimeError(f"uid {uid}: child error: {process.stderr.strip()}")
    return json.loads(process.stdout)


def assert_untrusted_cannot_bypass_file_root(uid, path):
    """Prove real OS DAC rejects bypass into THIS broker-owned effect root."""
    code = ("import os,sys; fd=os.open(sys.argv[1], "
            "os.O_CREAT|os.O_EXCL|os.O_WRONLY, 0o600); os.close(fd)")
    p = subprocess.run([sys.executable, "-c", code, str(path)],
                       capture_output=True, text=True,
                       preexec_fn=(lambda: os.setuid(uid)))
    assert p.returncode != 0, "untrusted UID could bypass the broker output root"
    assert not path.exists(), "untrusted write unexpectedly created an effect"


def disconnect_by_uid(uid, socketpath, data):
    program = (
        "import socket,sys; "
        "s=socket.socket(socket.AF_UNIX); s.connect(sys.argv[1]); "
        "s.shutdown(socket.SHUT_RD); s.sendall((sys.argv[2]+'\\n').encode()); "
        "s.shutdown(socket.SHUT_WR); s.close()"
    )
    subprocess.run([sys.executable, "-c", program, str(socketpath), json.dumps(data)],
                   check=True, preexec_fn=(lambda: os.setuid(uid)))


def main():
    if os.geteuid() != 0:
        raise SystemExit("root required to simulate separate real Linux UIDs")
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        root.chmod(0o755)
        # GitHub's checkout ancestors may be private to the runner UID.
        # Give the deliberately untrusted child ONLY the public RPC client
        # package in a separate readable directory, not the live source tree.
        childdir = root / "agent-import"
        childdir.mkdir(mode=0o755)
        shutil.copytree(Path(__file__).resolve().parents[1] / "trusted_stack",
                        childdir / "trusted_stack")
        state = root / "private"
        state.mkdir(mode=0o700)
        effectdir = state / "published"
        effectdir.mkdir(mode=0o700)
        assert_untrusted_cannot_bypass_file_root(AGENT, effectdir / "rogue.bin")
        sockpath = root / "trusted.sock"
        cmd = [sys.executable, "-m", "trusted_stack.server",
               "--db", str(state / "state.sqlite"),
               "--socket", str(sockpath),
               "--agents", str(AGENT),
               "--reviewers", str(REVIEWER),
               "--approvers", str(APPROVER),
               "--admins", "0",
               "--bootstrap-cap", "2",
               "--effect-root", str(effectdir)]
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
            checked = 0
            def call(uid, data, permitted):
                nonlocal checked
                reply = by_uid(uid, sockpath, data)
                assert reply["ok"] is permitted, (uid, data, reply)
                checked += 1
                return reply
            # An untrusted peer closes its receiving half before the reply.
            # Old serve() propagated BrokenPipeError and killed the broker.
            # Deliberately malformed frames cause no persistent state changes.
            for _ in range(8):
                disconnect_by_uid(AGENT, sockpath, {})
            assert call(0, {"op": "state"}, True)["result"]["releases"] == 0
            call(AGENT, {"op": "stage", "body_b64": base64.b64encode(content).decode()}, True)
            call(AGENT, {"op": "review", "digest": digest}, False)
            call(REVIEWER, {"op": "review", "digest": digest}, True)
            call(0, {"op": "issue_lease", "lease_id": "lease1", "agent_uid": AGENT,
                     "budget": 2, "expires": int(time.time()) + 500}, True)
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
            # A valid request commits even when its acknowledgment is lost.
            # Observe persistence through a separate trusted connection, then
            # demonstrate that retry never duplicates the committed release.
            disconnect_by_uid(AGENT, sockpath, release)
            assert call(0, {"op": "state"}, True)["result"] == {
                "global_cap": 2, "halted": False, "spent": 1, "releases": 1}
            call(AGENT, release, False)
            # A SECOND, independently signed nonce creates the narrowly
            # permitted real filesystem effect; the first record-only
            # release still counts against shared budget.
            call(APPROVER, {"op": "approve", "nonce": "n2", "digest": digest,
                            "destination": "staging/item", "agent_uid": AGENT,
                            "lease_id": "lease1", "expires": int(time.time()) + 400}, True)
            call(AGENT, {**release, "op": "effect_release", "nonce": "n2"}, True)
            publish = {"op": "publish_effect", "release_id": 2}
            call(AGENT, publish, False)
            call(OTHER, publish, False)
            assert call(0, publish, True)["result"]["file"] == "effect-000000000002.bin"
            assert (effectdir / "effect-000000000002.bin").read_bytes() == content
            call(0, publish, True)  # reply loss/retry cannot duplicate a file
            assert [p.name for p in effectdir.iterdir()] == ["effect-000000000002.bin"]
            assert (effectdir / "effect-000000000002.bin").stat().st_mode & 0o077 == 0
            call(0, {"op": "halt"}, True)
            call(0, publish, False)  # no new post-HALT publish operations
            call(AGENT, {"op": "stage", "body_b64": base64.b64encode(b"x").decode()}, False)
            assert call(0, {"op": "state"}, True)["result"] == {
                "global_cap": 2, "halted": True, "spent": 1, "releases": 1}
            print(f"PASS: {checked} real Unix peer-credential broker checks, "
                  "9 disconnected callers, 2 releases and 1 exact file effect")
        finally:
            proc.terminate()
            try:
                proc.communicate(timeout=4)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate(timeout=4)


if __name__ == "__main__":
    main()
