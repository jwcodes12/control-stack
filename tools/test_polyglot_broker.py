#!/usr/bin/env python3
"""Real Linux SO_PEERCRED exercise of two programming-language clients.

Requires root only to provision distinct disposable Linux OS UIDs. Does
not claim JavaScript process sandboxing or non-Linux transport coverage.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from trusted_stack.client import request

AGENT = 24611
REVIEWER = 24612
APPROVER = 24613
OTHER = 24614
ROOT = Path(__file__).resolve().parents[1]


def change_uid(uid):
    os.setgroups([])
    os.setgid(uid)
    os.setuid(uid)


def run_as(uid, command, *, cwd, input=None):
    result = subprocess.run(command, input=input, text=True, capture_output=True,
                            cwd=cwd, timeout=20, preexec_fn=lambda: change_uid(uid))
    if result.returncode:
        raise AssertionError("client failed to complete an RPC")
    parsed = json.loads(result.stdout)
    if type(parsed) is not dict or type(parsed.get("ok")) is not bool:
        raise AssertionError("client returned malformed RPC result")
    return parsed


def js(uid, node, script, sock, request_obj, cwd):
    return run_as(uid, [node, str(script), str(sock)],
                  input=json.dumps(request_obj), cwd=cwd)


def python(uid, sock, request_obj, cwd):
    program = ("import json,sys;from trusted_stack.client import request;"
               "print(json.dumps(request(sys.argv[1], json.loads(sys.stdin.read()))))")
    return run_as(uid, [sys.executable, "-c", program, str(sock)],
                  input=json.dumps(request_obj), cwd=cwd)


def main():
    if os.geteuid() != 0 or not sys.platform.startswith("linux"):
        raise SystemExit("root on Linux required")
    node = shutil.which("node")
    if not node:
        raise SystemExit("Node.js required; no silent skip")
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        root.chmod(0o755)
        worker = root / "worker"
        worker.mkdir(mode=0o755)
        shutil.copytree(ROOT / "trusted_stack", worker / "trusted_stack")
        client = worker / "control_stack_client.mjs"
        shutil.copy2(ROOT / "interop/node/control_stack_client.mjs", client)
        dbdir = root / "private"
        dbdir.mkdir(mode=0o700)
        socket = root / "control.sock"
        proc = subprocess.Popen([
            sys.executable, "-m", "trusted_stack.server",
            "--db", str(dbdir / "db.sqlite"), "--socket", str(socket),
            "--agents", str(AGENT), "--reviewers", str(REVIEWER),
            "--approvers", str(APPROVER), "--admins", "0",
            "--bootstrap-cap", "2",
        ], cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
           text=True)
        try:
            for _ in range(100):
                if socket.exists():
                    break
                if proc.poll() is not None:
                    raise AssertionError("broker startup failure")
                time.sleep(.04)
            else:
                raise AssertionError("broker socket was not created")
            data = b"same reviewed bytes across Node and Python"
            digest = hashlib.sha256(data).hexdigest()
            stage = {"op": "stage", "body_b64": base64.b64encode(data).decode("ascii")}
            assert js(AGENT, node, client, socket, stage, worker) == {
                "ok": True, "result": digest}
            assert python(REVIEWER, socket, {"op": "review", "digest": digest},
                          worker)["ok"] is True
            expiry = int(time.time()) + 200
            assert request(socket, {
                "op": "issue_lease", "lease_id": "polyglot",
                "agent_uid": AGENT, "budget": 1, "expires": expiry
            })["ok"] is True
            assert python(APPROVER, socket, {
                "op": "approve", "nonce": "one-use-polyglot", "digest": digest,
                "destination": "trusted/output", "agent_uid": AGENT,
                "lease_id": "polyglot", "expires": expiry
            }, worker)["ok"] is True
            effect = {"op": "effect_release", "nonce": "one-use-polyglot",
                      "digest": digest, "destination": "trusted/output",
                      "lease_id": "polyglot"}
            assert js(OTHER, node, client, socket, effect, worker) == {
                "ok": False, "error": "DENIED"}
            assert js(AGENT, node, client, socket,
                      {**effect, "uid": 0}, worker)["ok"] is False
            assert js(AGENT, node, client, socket, effect, worker) == {
                "ok": True, "result": 1}
            assert python(AGENT, socket, effect, worker)["ok"] is False
            assert request(socket, {"op": "state"})["result"] == {
                "global_cap": 2, "halted": False, "spent": 1, "releases": 1}
            assert request(socket, {"op": "halt"})["ok"] is True
            assert js(AGENT, node, client, socket, stage, worker)["ok"] is False
            print("PASS: Node and Python have identical broker admission, "
                  "SO_PEERCRED identity, one-use/HALT semantics")
        finally:
            proc.terminate()
            try:
                proc.communicate(timeout=4)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate(timeout=4)


if __name__ == "__main__":
    main()
