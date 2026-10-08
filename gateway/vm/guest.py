"""Trusted guest supervisor. The honest agents have no guest network or state access."""
from __future__ import annotations

import hashlib
import json
import os
import socket
import subprocess
import sys
import time
import traceback
import threading
from pathlib import Path

sys.path.insert(0, "/opt/sc01")
from gateway import Channel, Gateway, GatewayError, LifetimeLedger, Schema

APP = Path("/opt/sc01")
CONTRACT = json.loads((APP / "contract.json").read_text())
ROLE = Path("/etc/sc01-role").read_text().strip()
MAX_BYTES = 64000
BWRAP = ["/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
         "--clearenv", "--cap-drop", "ALL", "--ro-bind", "/usr", "/usr",
         "--ro-bind", "/lib", "/lib", "--symlink", "usr/bin", "/bin",
         "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
         "--setenv", "PATH", "/usr/bin"]


def emit(item):
    print("SC01 " + json.dumps(item, separators=(",", ":")), flush=True)


def agent(name, item, deadline):
    cmd = BWRAP + ["--ro-bind", str(APP / name), "/agent.py",
                   "/usr/bin/python3", "-I", "/agent.py"]
    try:
        p = subprocess.run(cmd, input=json.dumps(item) + "\n", capture_output=True,
                           text=True, timeout=deadline)
        result = {"stdout": p.stdout, "ok": p.returncode == 0, "timed_out": False}
        if name == "preflight.py":
            result["preflight_stderr"] = p.stderr[:2000]
        return result
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        return {"stdout": out, "ok": False, "timed_out": True}


def preflight():
    p = agent("preflight.py", {}, 10)
    if not p["ok"]:
        raise RuntimeError("agent namespace preflight unavailable: " + p.get("preflight_stderr", "timeout"))
    info = json.loads(p["stdout"])
    info["host_netns"] = Path("/proc/self/ns/net").stat().st_ino
    info["host_pidns"] = Path("/proc/self/ns/pid").stat().st_ino
    if not (info["netns"] != info["host_netns"] and info["pidns"] != info["host_pidns"]
            and int(info["effective_capabilities"], 16) == 0
            and info["no_new_privileges"] == "1" and info["interfaces"] == ["lo"]
            and len(info["routes4"].splitlines()) == 1):
        raise RuntimeError("agent namespace preflight failed")
    return {"role": ROLE, "boot_id": Path("/proc/sys/kernel/random/boot_id").read_text().strip(),
            "kernel": os.uname().release, "agent": info,
            "guest_routes4": Path("/proc/net/route").read_text(),
            "guest_addresses": subprocess.check_output(["/bin/busybox", "ip", "-4", "addr", "show"], text=True),
            "guest_interfaces": sorted(p.name for p in Path("/sys/class/net").iterdir()),
            "source_hashes": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in APP.iterdir() if p.is_file()}}


def recv_line(stream):
    line = stream.readline(MAX_BYTES + 1)
    if not line or len(line) > MAX_BYTES or not line.endswith(b"\n"):
        raise RuntimeError("invalid trusted transport frame")
    return json.loads(line)


def network_info():
    return {"addresses": subprocess.check_output(["/bin/busybox", "ip", "addr", "show"], text=True),
            "neighbors": Path("/proc/net/arp").read_text(),
            "counters": {p.name: p.read_text().strip()
                         for p in Path("/sys/class/net/eth0/statistics").iterdir()}}


def receiver_management():
    for line in sys.stdin:
        request = json.loads(line)
        if request.get("op") == "network_info":
            emit({"event": "response", "id": request["id"], "result": network_info()})
        else:
            emit({"event": "error", "error_type": "InvalidManagementOperation"})


def receiver():
    server = socket.socket()
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("192.0.2.2", 9401))
    server.listen(1)
    emit({"event": "ready", "preflight": preflight()})
    threading.Thread(target=receiver_management, daemon=True).start()
    while True:
        with server.accept()[0] as conn:
            conn.settimeout(15)
            with conn.makefile("rwb", buffering=0) as stream:
                request = recv_line(stream)
                if request["input"] == {"infrastructure_health": True}:
                    stream.write(b'{"infrastructure_health":true}\n')
                    continue
                p = agent("repair.py", request["input"], CONTRACT["deadline_seconds"])
                try:
                    reply = json.loads(p["stdout"])
                except ValueError:
                    reply = None
                stream.write(json.dumps({"receiver_reply": reply, "receiver_ok": p["ok"],
                                         "receiver_timed_out": p["timed_out"]}).encode() + b"\n")


def receiver_call(item):
    with socket.create_connection(("192.0.2.2", 9401), timeout=15) as conn:
        with conn.makefile("rwb", buffering=0) as stream:
            stream.write(json.dumps({"input": item}).encode() + b"\n")
            return recv_line(stream)


def channel():
    c = CONTRACT["channel"]
    return {c["name"]: Channel(c["name"], Schema(((c["field"], tuple(c["values"])),)), c["slots"])}


def episode(item, ledger):
    deadline = CONTRACT["deadline_seconds"]
    mode, fault = item["condition"], item["fault"]
    if mode not in ("baseline", "mediated") or type(fault) is not int or not 0 <= fault < 8:
        raise ValueError("invalid trusted task")
    # Charge before launching a sender. Baseline uses an independent secret.
    g = Gateway(channel(), budget_bits=CONTRACT["lifetime_budget_bits"], ledger=ledger,
                lineage=item["lineage"], require_lifetime=True) if mode == "mediated" else None
    start = time.monotonic()
    sender_input = {"mode": mode, "secret": item["secret"],
                    "program": "def calc(a, b):\n    return " + CONTRACT["fault_expressions"][fault] + "\n",
                    "probes": CONTRACT["diagnostic_inputs"], "catalog": CONTRACT["fault_expressions"]}
    sender = agent("diagnose.py", sender_input, deadline)
    if mode == "baseline":
        try:
            diagnostic = json.loads(sender["stdout"]) if len(sender["stdout"].encode()) <= MAX_BYTES else None
        except ValueError:
            diagnostic = None
        receiver_input = {"mode": mode, "catalog": CONTRACT["fault_expressions"], "diagnostic": diagnostic}
    else:
        if len(sender["stdout"].encode()) > MAX_BYTES:
            g.act()
        else:
            for line in sender["stdout"].splitlines():
                try:
                    msg = json.loads(line)
                except ValueError:
                    g.act()
                    continue
                if type(msg) is dict and set(msg) == {"op", "channel", "payload"} and msg["op"] == "send":
                    g.send(msg["channel"], msg["payload"])
                else:
                    g.act()
        g.close()
        view = {k: [list(x) if x is not None else None for x in v] for k, v in g.deliver().items()}
        receiver_input = {"mode": mode, "view": view}
    # Preserve the original 0.25s deadline and fixed sender-window schedule.
    time.sleep(max(0, deadline - (time.monotonic() - start)))
    result = receiver_call(receiver_input)
    result.update(sender_ok=sender["ok"], sender_timed_out=sender["timed_out"],
                  elapsed_seconds=time.monotonic() - start)
    if g is not None:
        result.update(view=view, alerts=list(g.alerts), false_blank=view["repair"] == [None])
    return result


def sender_gateway():
    emit({"event": "ready", "preflight": preflight()})
    ledger = None
    for line in sys.stdin:
        try:
            request = json.loads(line)
            op = request["op"]
            if op == "start":
                run_id = request["run_id"]
                if ledger is not None or not run_id.isalnum():
                    raise ValueError("invalid run initialization")
                ledger = LifetimeLedger.create(Path("/state") / (run_id + ".sqlite3"), CONTRACT["lifetime_budget_bits"])
                result = {"started": True}
            elif op == "health":
                result = receiver_call({"infrastructure_health": True})
            elif op == "network_info":
                result = network_info()
            elif op == "episode" and ledger is not None:
                result = episode(request, ledger)
            elif op == "usage" and ledger is not None:
                reopened = LifetimeLedger(ledger.path, CONTRACT["lifetime_budget_bits"])
                product, admissions = reopened.usage(request["lineage"])
                rejected = False
                try:
                    Gateway(channel(), budget_bits=CONTRACT["lifetime_budget_bits"], ledger=reopened,
                            lineage=request["lineage"], require_lifetime=True)
                except GatewayError:
                    rejected = True
                result = {"ledger_product": product, "admissions": admissions, "sixth_episode_rejected": rejected}
            else:
                raise ValueError("invalid trusted operation")
            emit({"event": "response", "id": request["id"], "result": result})
        except Exception as exc:
            # Fixed error type, never reflect task inputs or secrets into logs.
            frame = traceback.extract_tb(exc.__traceback__)[-1]
            emit({"event": "error", "error_type": type(exc).__name__,
                  "errno": exc.errno if isinstance(exc, OSError) else None,
                  "where": {"file": Path(frame.filename).name, "line": frame.lineno, "function": frame.name}})


if __name__ == "__main__":
    if ROLE == "A":
        sender_gateway()
    elif ROLE == "B":
        receiver()
    else:
        raise RuntimeError("unknown guest role")
