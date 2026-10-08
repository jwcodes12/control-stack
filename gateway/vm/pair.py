"""Boot the exact provisioned QEMU commands; collect live configuration evidence."""
from __future__ import annotations

import argparse
import json
import os
import queue
import shutil
import socket
import subprocess
import threading
import time
from datetime import datetime, timezone
from pathlib import Path

from provision import canonical_hash, sha


def qmp(path, commands):
    with socket.socket(socket.AF_UNIX) as conn:
        conn.settimeout(10)
        conn.connect(str(path))
        with conn.makefile("rwb", buffering=0) as stream:
            greeting = json.loads(stream.readline())
            def call(name):
                stream.write(json.dumps({"execute": name}).encode() + b"\n")
                while True:
                    result = json.loads(stream.readline())
                    if "event" not in result:
                        if "error" in result:
                            raise RuntimeError("QMP rejected " + name)
                        return result["return"]
            call("qmp_capabilities")
            return {"greeting": greeting, **{name: call(name) for name in commands}}


def tcp_states(port):
    """States of host TCP sockets on 127.0.0.1:port, read from /proc/net/tcp WITHOUT connecting (a probe connection
    would consume the listening QEMU's single accept)."""
    states = []
    for line in Path("/proc/net/tcp").read_text().splitlines()[1:]:
        fields = line.split()
        local, remote, state = fields[1], fields[2], fields[3]
        if local == "0100007F:%04X" % port or remote == "0100007F:%04X" % port:
            states.append((local, remote, state))
    return states


def link_endpoint(spec):
    """("listen" | "connect", port) of the single socket netdev"""
    arg = spec["qemu_argv"][spec["qemu_argv"].index("-netdev") + 1]
    for part in arg.split(","):
        if part.startswith(("listen=", "connect=")):
            kind, address = part.split("=", 1)
            return kind, int(address.rsplit(":", 1)[1])
    raise RuntimeError("no socket netdev endpoint")


def wait_for(predicate, timeout, what, vm):
    start = time.monotonic()
    while time.monotonic() - start < timeout:
        if predicate():
            return round(time.monotonic() - start, 3)
        if vm.process.poll() is not None:
            raise RuntimeError(vm.spec["name"] + " exited while waiting for " + what)
        time.sleep(0.05)
    raise RuntimeError("timed out waiting for " + what)


class VM:
    def __init__(self, spec):
        self.spec, self.messages, self.boot_log = spec, queue.Queue(), []
        self.process = subprocess.Popen([shutil.which("taskset"), "-c",
                                         ",".join(map(str, spec["cpu_affinity"])), *spec["qemu_argv"]],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.reader = threading.Thread(target=self._read, daemon=True)
        self.reader.start()
        self.ready = None

    def _read(self):
        for line in self.process.stdout:
            if line.startswith("SC01 "):
                try:
                    self.messages.put(json.loads(line[5:]))
                except ValueError:
                    self.boot_log.append("invalid supervisor JSON")
            else:
                self.boot_log.append(line.rstrip())
        self.messages.put({"event": "exited", "returncode": self.process.wait()})

    def await_ready(self):
        message = self.messages.get(timeout=180)
        if message.get("event") != "ready":
            raise RuntimeError(self.spec["name"] + " not ready: " + str(message) + "\n" + "\n".join(self.boot_log[-30:]))
        self.ready = message["preflight"]

    def request(self, item):
        self.process.stdin.write(json.dumps(item) + "\n")
        self.process.stdin.flush()
        result = self.messages.get(timeout=45)
        if result.get("event") != "response" or result.get("id") != item["id"]:
            raise RuntimeError("guest supervisor response failure: " + str(result))
        return result["result"]

    def snapshot(self):
        pid = self.process.pid
        cmdline = (Path("/proc") / str(pid) / "cmdline").read_bytes().rstrip(b"\0").decode().split("\0")
        threads = {}
        for task in sorted((Path("/proc") / str(pid) / "task").iterdir()):
            threads[task.name] = sorted(os.sched_getaffinity(int(task.name)))
        socket_arg = self.spec["qemu_argv"][self.spec["qemu_argv"].index("-qmp") + 1]
        state = qmp(Path(socket_arg.removeprefix("unix:").split(",")[0]),
                    ["query-status", "query-cpus-fast", "query-block", "query-chardev", "query-memory-devices"])
        return {"pid": pid, "actual_argv": cmdline, "thread_cpu_affinity": threads,
                "qmp": state, "guest": self.ready, "boot_log": self.boot_log}

    def stop(self):
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)


class Pair:
    def __init__(self, config_path):
        self.path = Path(config_path)
        self.config = json.loads(self.path.read_text())
        self.vms = []
        self.link = {}

    def __enter__(self):
        # QEMU's `-netdev socket,connect=` tries once and never retries: if the connecting guest starts before the
        # listening guest has bound its port, the link stays down for the whole boot with no error (observed
        # 2026-10-08: both guests transmit, neither receives). So start the listener first, wait for LISTEN, then
        # start the connector and require an ESTABLISHED host socket pair before any guest traffic.
        try:
            specs = sorted(self.config["vms"], key=lambda spec: link_endpoint(spec)[0] != "listen")
            for spec in specs:
                kind, port = link_endpoint(spec)
                vm = VM(spec)
                self.vms.append(vm)
                if kind == "listen":
                    self.link["listen_ready_s"] = wait_for(
                        lambda: any(state == "0A" for _, _, state in tcp_states(port)), 60, "link LISTEN", vm)
                else:
                    self.link["established_s"] = wait_for(
                        lambda: sum(state == "01" for _, _, state in tcp_states(port)) >= 2, 60,
                        "link ESTABLISHED", vm)
            self.link["port"] = port
            self.link["host_sockets_at_start"] = tcp_states(port)
            self.vms.sort(key=lambda vm: [spec["name"] for spec in self.config["vms"]].index(vm.spec["name"]))
            for vm in self.vms:
                vm.await_ready()
            if self.vms[0].ready["boot_id"] == self.vms[1].ready["boot_id"]:
                raise RuntimeError("guest boot identities are not distinct")
            return self
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def __exit__(self, *_):
        for vm in reversed(self.vms):
            vm.stop()

    def receipt(self):
        return {"schema": "sc01-qemu-provision-receipt/1",
                "captured_at": datetime.now(timezone.utc).isoformat(),
                "config_hash": canonical_hash(self.config), "config": self.config,
                "live": {vm.spec["name"]: vm.snapshot() for vm in self.vms},
                "link": {**self.link, "host_sockets_now": tcp_states(self.link["port"])},
                "verdict": "CONDITIONAL", "scope": "Guest boot and configuration; no channel measurement"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--health", type=int, default=0,
                        help="also send N fixed infrastructure health requests over the guest link and record them")
    args = parser.parse_args()
    if args.receipt.exists():
        raise SystemExit("refusing to overwrite a receipt")
    with Pair(args.config) as pair:
        receipt = pair.receipt()
        if args.health:
            attempts = []
            for i in range(args.health):
                try:
                    attempts.append({"status": "ok", "result": pair.vms[0].request({"id": f"health-{i}", "op": "health"})})
                except Exception as exc:
                    attempts.append({"status": "fail", "reason": str(exc)})
            receipt["transport_attempts"] = attempts
        args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
        print("Booted separate guest kernels; config hash", receipt["config_hash"])


if __name__ == "__main__":
    main()
