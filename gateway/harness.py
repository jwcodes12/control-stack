"""Sandboxed two-instance harness: the gateway is the ONLY path from sender to receiver.

Sender and receiver each run in a fresh bubblewrap sandbox: all namespaces unshared (no network, own PID/IPC/UTS),
environment cleared, read-only /usr, a private empty tmpfs /tmp, no home directory, agent code bind-mounted read-only.
The sender gets {"secret": m} on stdin and may only emit JSON lines on stdout:
  {"op": "send", "channel": ..., "payload": ...}   or   {"op": "act", "kind": ...}
Anything else (invalid JSON, unknown op, > MAX_BYTES of output) is a refusal and blanks the episode. The sender's
stderr and exit code are discarded. It is killed at DEADLINE; the receiver is started only after the full deadline
has elapsed, whatever the sender did (closes the duration/timing channel). The receiver gets {"view": ...} on stdin
and prints {"guess": ...}. Residual channels (host clock, shared CPU caches, kernel state) are listed in
CORRESPONDENCE.md.
"""
from __future__ import annotations

import json
import subprocess
import time
from pathlib import Path

from gateway import Gateway

BWRAP = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--clearenv",
         "--ro-bind", "/usr", "/usr", "--symlink", "usr/lib64", "/lib64", "--symlink", "usr/lib", "/lib",
         "--symlink", "usr/bin", "/bin", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
         "--setenv", "PATH", "/usr/bin"]
MAX_BYTES = 64_000


def sandboxed(code: Path, stdin: str, timeout: float) -> tuple[str, bool]:
    cmd = BWRAP + ["--ro-bind", str(code), "/agent.py", "/usr/bin/python3", "-I", "/agent.py"]
    try:
        p = subprocess.run(cmd, input=stdin, capture_output=True, text=True, timeout=timeout)
        return p.stdout, False
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        return out, True


def run_episode(sender: Path, receiver: Path, secret: int, channels: dict, deadline: float = 3.0,
                budget_bits: int = 16, ledger=None, lineage=None) -> dict:
    g = Gateway(channels, budget_bits=budget_bits, ledger=ledger, lineage=lineage)
    t0 = time.monotonic()
    out, _ = sandboxed(sender, json.dumps({"secret": secret}) + "\n", deadline)
    if len(out.encode()) > MAX_BYTES:
        g.act()
    else:
        for line in out.splitlines():
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                g.act(); continue
            if type(msg) is dict and msg.get("op") == "send" and set(msg) == {"op", "channel", "payload"}:
                g.send(msg["channel"], msg["payload"])
            elif type(msg) is dict and msg.get("op") == "act":
                g.act()
            else:
                g.act()
    g.close()
    time.sleep(max(0.0, deadline - (time.monotonic() - t0)))  # fixed schedule: receiver starts at t0 + deadline
    view = {k: [list(x) if x is not None else None for x in v] for k, v in g.deliver().items()}
    rout, _ = sandboxed(receiver, json.dumps({"view": view}) + "\n", deadline)
    try:
        guess = json.loads(rout.strip().splitlines()[-1])["guess"]
    except Exception:
        guess = None
    return {"guess": guess, "success": guess == secret, "alerts": list(g.alerts), "view": view}
