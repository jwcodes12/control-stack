#!/usr/bin/env python3
"""Fail-closed checker of a deliberately narrow QEMU guest configuration profile.

This checks configured resource separation, not complete observations or leakage.
Unknown QEMU flags/devices are rejected instead of trusting an inventory summary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from provision import canonical_hash, sha


class IsolationError(ValueError):
    def __init__(self, code, message):
        super().__init__(code + ": " + message)
        self.code = code


def need(condition, code, message):
    if not condition:
        raise IsolationError(code, message)


def fields(text):
    parts = text.split(",")
    result = {}
    for part in parts:
        key, sep, value = part.partition("=")
        need(key not in result, "unknown_config", "duplicate backend property")
        result[key] = value if sep else None
    return result


def options(argv):
    single = {"-no-user-config", "-nodefaults", "-no-reboot"}
    valued = {"-machine", "-accel", "-cpu", "-smp", "-m", "-object", "-display",
              "-monitor", "-serial", "-qmp", "-kernel", "-initrd", "-append", "-drive", "-device", "-netdev"}
    need(type(argv) is list and all(type(x) is str for x in argv) and len(argv) > 1,
         "unknown_config", "invalid QEMU argv")
    result, index = {}, 1
    while index < len(argv):
        flag = argv[index]
        if flag in {"-fsdev", "-virtfs", "-chardev"}:
            raise IsolationError("shared_filesystem", "host filesystem/chardev passthrough forbidden")
        need(flag in single | valued, "unknown_config", "unapproved QEMU flag " + flag)
        if flag in single:
            result.setdefault(flag, []).append(None)
            index += 1
        else:
            need(index + 1 < len(argv), "unknown_config", "missing option value")
            result.setdefault(flag, []).append(argv[index + 1])
            index += 2
    for flag in single:
        need(result.get(flag) == [None], "unknown_config", "required defaults disabling absent/duplicated")
    for flag in valued - {"-device", "-netdev", "-object"}:
        need(len(result.get(flag, [])) == 1, "unknown_config", "missing/duplicated " + flag)
    need(len(result.get("-netdev", [])) == 1, "network_paths", "exactly one network backend required")
    need(len(result.get("-object", [])) == 1, "shared_memory", "exactly one private RAM backend required")
    return result


def validate_paths(resources, require_files=False):
    names, inodes = set(), set()
    for resource in resources:
        path = Path(resource).resolve()
        need(str(path) not in names, "shared_file", "shared disk/boot/management path")
        names.add(str(path))
        if path.exists():
            stat = path.stat()
            key = (stat.st_dev, stat.st_ino)
            need(key not in inodes and stat.st_nlink == 1, "shared_file", "inode alias or hardlinked resource")
            inodes.add(key)
        elif require_files:
            raise IsolationError("missing_resource", "missing boot/disk file " + str(path))


def check(config, receipt=None, files=False):
    need(config.get("schema") == "sc01-qemu-pair/1" and config.get("accelerator") == "tcg",
         "unknown_config", "unsupported profile")
    vms = config.get("vms")
    need(type(vms) is list and len(vms) == 2, "unknown_config", "exactly two VMs required")
    need([v.get("name") for v in vms] == ["VM-A", "VM-B"], "unknown_config", "role ordering")
    pins, resources, sockets, endpoints = set(), [], [], []
    for vm in vms:
        cpus = vm.get("cpu_affinity")
        need(type(cpus) is list and len(cpus) == 1 and type(cpus[0]) is int and cpus[0] >= 0,
             "cpu_pinning", "one explicit host CPU per VM required")
        need(not pins.intersection(cpus), "cpu_overlap", "overlapping VM CPU pinning")
        need(vm.get("numa_node") == 0 and cpus[0] in config["host"]["numa"]["0"],
             "cpu_pinning", "pin outside recorded NUMA layout")
        pins.update(cpus)
        opt = options(vm["qemu_argv"])
        need(vm["qemu_argv"][0] == config["qemu"]["path"], "unknown_config", "hypervisor path differs")
        need(opt["-machine"] == ["virt-11.1,memory-backend=ram"] and opt["-accel"] == ["tcg,thread=single"]
             and opt["-cpu"] == ["cortex-a57"] and opt["-smp"] == ["1"] and opt["-m"] == ["512M"],
             "unknown_config", "unapproved machine/CPU/memory profile")
        ram = fields(opt["-object"][0])
        need(ram == {"memory-backend-ram": None, "id": "ram", "size": "512M", "merge": "off",
                     "prealloc": "on", "share": "off"}, "shared_memory", "shared/file-backed/merged RAM forbidden")
        need(opt["-display"] == ["none"] and opt["-monitor"] == ["none"] and opt["-serial"] == ["stdio"],
             "management", "unapproved display/serial/monitor path")
        need(opt["-append"] == ["console=ttyAMA0 rdinit=/init panic=-1 quiet"],
             "unknown_config", "unapproved guest startup")
        qmp = opt["-qmp"][0]
        need(qmp.startswith("unix:") and qmp.endswith(",server=on,wait=off"),
             "management", "QMP must be an independent local socket")
        sockets.append(qmp[5:].split(",")[0])
        drive = fields(opt["-drive"][0])
        need(set(drive) == {"file", "format", "if", "id"} and drive["format"] == "raw"
             and drive["if"] == "none" and drive["id"] == "state", "shared_disk", "only a private raw disk permitted")
        paths = {"kernel": opt["-kernel"][0], "initramfs.gz": opt["-initrd"][0], "state.raw": drive["file"]}
        need(set(vm["images"]) == set(paths), "unknown_config", "unexpected image inventory")
        for name, path in paths.items():
            need(path == vm["images"][name]["path"], "unknown_config", "argv/image inventory mismatch")
            need(re.fullmatch(r"[0-9a-f]{64}", vm["images"][name]["initial_sha256"]) is not None,
                 "image_binding", "image hash missing")
            if files and name != "state.raw":
                need(sha(path) == vm["images"][name]["initial_sha256"], "image_binding", "boot image hash differs")
        resources.extend(paths.values())
        net = fields(opt["-netdev"][0])
        direction = "listen" if vm["name"] == "VM-A" else "connect"
        need(set(net) == {"socket", "id", direction} and net["id"] == "link"
             and net["socket"] is None and re.fullmatch(r"127\.0\.0\.1:[0-9]+", net[direction]) is not None,
             "network_paths", "only paired local socket networking permitted")
        endpoints.append(net[direction])
        devices = opt.get("-device", [])
        need(len(devices) == 2, "unknown_device", "extra or missing VM devices")
        need(devices[0] == "virtio-blk-device,drive=state", "unknown_device", "unapproved disk device")
        mac = "52:54:00:00:00:01" if vm["name"] == "VM-A" else "52:54:00:00:00:02"
        need(devices[1] in {"virtio-net-device,netdev=link,mac=" + mac,
                           "virtio-net-pci,netdev=link,mac=" + mac},
             "unknown_device", "unapproved network/shared-memory/filesystem device")
    need(endpoints[0] == endpoints[1], "network_paths", "network endpoints are not one pair")
    validate_paths(resources, files)
    validate_paths(resources + sockets)
    if files:
        need(sha(config["qemu"]["path"]) == config["qemu"]["sha256"], "hypervisor_binding", "QEMU binary hash differs")
    if receipt is not None:
        need(receipt["config"] == config and receipt["config_hash"] == canonical_hash(config),
             "receipt_binding", "receipt/config hash mismatch")
        need(set(receipt["live"]) == {"VM-A", "VM-B"}, "receipt_binding", "missing live VMs")
        if "link" in receipt:
            # the single guest link as seen by the host: one listener, one mirrored ESTABLISHED pair, nothing else
            port = int(net_endpoint_port(vms[0]))
            here = "0100007F:%04X" % port
            for key in ("host_sockets_at_start", "host_sockets_now"):
                rows = receipt["link"][key]
                listens = [r for r in rows if r[2] == "0A"]
                active = [r for r in rows if r[2] in {"01", "02", "03"}]
                need(receipt["link"]["port"] == port and len(listens) == 1 and listens[0][0] == here,
                     "network_paths", "link listener differs")
                need(len(active) == 2 and {active[0][0], active[0][1]} == {active[1][0], active[1][1]}
                     and here in {active[0][0], active[0][1]} and active[0][0] == active[1][1],
                     "network_paths", "link is not exactly one established guest pair")
        boot_ids = set()
        names = {"gateway/gateway.py": "gateway.py", "gateway/scenario/contract.json": "contract.json",
                 "gateway/scenario/agents/diagnose.py": "diagnose.py", "gateway/scenario/agents/repair.py": "repair.py",
                 "gateway/scenario/agents/preflight.py": "preflight.py", "gateway/vm/guest.py": "guest.py"}
        for vm in vms:
            live = receipt["live"][vm["name"]]
            need(live["actual_argv"] == vm["qemu_argv"], "live_config", "actual process argv differs")
            need(bool(live["thread_cpu_affinity"]) and all(v == vm["cpu_affinity"]
                 for v in live["thread_cpu_affinity"].values()), "cpu_overlap", "live thread affinity differs")
            qmp, guest = live["qmp"], live["guest"]
            need(qmp["query-status"]["status"] == "running" and len(qmp["query-cpus-fast"]) == 1,
                 "live_config", "VM not running with one CPU")
            need(qmp["query-memory-devices"] == [], "shared_memory", "extra memory device")
            blocks = qmp["query-block"]
            need(len(blocks) == 1 and blocks[0]["inserted"]["file"] == vm["images"]["state.raw"]["path"]
                 and blocks[0]["inserted"]["drv"] == "raw"
                 and blocks[0]["inserted"]["backing_file_depth"] == 0,
                 "shared_disk", "live disk/backing configuration differs")
            chardevs = {c["label"]: c["filename"] for c in qmp["query-chardev"]}
            own_socket = sockets[0 if vm["name"] == "VM-A" else 1]
            need(len(qmp["query-chardev"]) == 2 and chardevs == {
                "serial0": "stdio", "compat_monitor0": "unix:" + own_socket + ",server=on"},
                "management", "unapproved live chardev path")
            need(guest["guest_interfaces"] == ["eth0", "lo"], "network_paths", "extra guest interface")
            boot_id = guest["boot_id"]
            need(boot_id not in boot_ids, "guest_kernel", "same guest boot identity")
            boot_ids.add(boot_id)
            info = guest["agent"]
            need(info["netns"] != info["host_netns"] and info["pidns"] != info["host_pidns"]
                 and int(info["effective_capabilities"], 16) == 0 and info["no_new_privileges"] == "1"
                 and info["interfaces"] == ["lo"] and len(info["routes4"].splitlines()) == 1,
                 "guest_agent", "agent namespace/capability/network check failed")
            need(all(guest["source_hashes"].get(name) == config["source_hashes"][rel]
                     for rel, name in names.items()), "image_binding", "loaded guest application source differs")
    return {"configuration_check": "pass", "config_hash": canonical_hash(config),
            "live_receipt_check": "pass-historical" if receipt else "not-requested",
            "file_check": "pass" if files else "not-requested",
            "scope": "configured resources only; shared physical/host effects and complete observations unresolved"}


def net_endpoint_port(vm):
    arg = vm["qemu_argv"][vm["qemu_argv"].index("-netdev") + 1]
    return next(p.split("=", 1)[1].rsplit(":", 1)[1] for p in arg.split(",") if p.startswith(("listen=", "connect=")))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--files", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = check(json.loads(args.config.read_text()),
                       json.loads(args.receipt.read_text()) if args.receipt else None, args.files)
        result.update(checker_sha256=sha(Path(__file__)), captured_at=datetime.now(timezone.utc).isoformat())
        if args.receipt:
            result["provision_receipt_sha256"] = sha(args.receipt)
        if args.output:
            need(not args.output.exists(), "receipt_binding", "refusing to replace checker receipt")
            args.output.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result, sort_keys=True))
        return 0
    except (IsolationError, KeyError, ValueError, OSError, TypeError) as exc:
        print("FAIL:", exc, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
