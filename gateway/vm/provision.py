#!/usr/bin/env python3
"""Create two independent QEMU TCG images/configs from hash-pinned Alpine inputs.

Run as root to assemble guest file ownership. No host network/ACL configuration.
Use pair.py afterwards to boot and record effective QMP/CPU configuration.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def fetch(entry, path):
    if not path.exists():
        with urllib.request.urlopen(entry["url"], timeout=60) as response, path.open("wb") as stream:
            shutil.copyfileobj(response, stream)
    if sha(path) != entry["sha256"]:
        raise RuntimeError("pinned download mismatch: " + path.name)
    return path


def image(root, path):
    names = ["."]
    for directory, dirs, files in os.walk(root):
        dirs.sort()
        files.sort()
        names.extend(str((Path(directory) / name).relative_to(root)) for name in dirs + files)
    p = subprocess.run(["cpio", "--quiet", "-o", "-H", "newc", "-0", "--owner=0:0"],
                       cwd=root, input=("\0".join(names) + "\0").encode(), capture_output=True, check=True)
    path.write_bytes(gzip.compress(p.stdout, compresslevel=1, mtime=0))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--assets", type=Path, default=Path("/var/tmp/sc01-vm-assets"))
    parser.add_argument("--qemu", type=Path, default=Path("/home/linuxbrew/.linuxbrew/bin/qemu-system-aarch64"))
    parser.add_argument("--port", type=int, default=19401)
    args = parser.parse_args()
    if os.geteuid() != 0:
        raise SystemExit("root required only for image assembly; boot pair as your normal user")
    if args.output.exists():
        raise SystemExit("refusing an existing pair directory; never reset state")
    qemu = args.qemu.resolve(strict=True)
    if b"tcg" not in subprocess.check_output([str(qemu), "-accel", "help"]):
        raise RuntimeError("QEMU TCG unavailable")
    args.output.mkdir(parents=True)
    args.assets.mkdir(parents=True, exist_ok=True)
    lock = json.loads((HERE / "image.lock.json").read_text())
    root = args.output / "build-root"
    root.mkdir()
    archive = fetch(lock["minirootfs"], args.assets / "minirootfs.tar.gz")
    subprocess.run(["tar", "-xzf", str(archive), "-C", str(root)], check=True)
    static_apk = fetch(lock["apk_static"], args.assets / "apk-tools-static.apk")
    static_bin = args.assets / "apk.static"
    with tarfile.open(static_apk) as tar:
        member = next(m for m in tar.getmembers() if m.name.endswith("/apk.static"))
        static_bin.write_bytes(tar.extractfile(member).read())
    static_bin.chmod(0o755)
    if sha(static_bin) != lock["apk_static"]["binary_sha256"]:
        raise RuntimeError("static APK tool mismatch")
    packages = []
    for entry in lock["packages"]:
        cached = args.assets / "packages" / entry["cache_filename"]
        cached.parent.mkdir(exist_ok=True)
        packages.append(str(fetch(entry, cached)))
    subprocess.run([str(static_bin), "--root", str(root), "--arch", "aarch64", "--no-network",
                    "--no-scripts", "--initdb", "add", *packages], check=True)
    app = root / "opt/sc01"
    app.mkdir(parents=True)
    copies = {"gateway/gateway.py": "gateway.py", "gateway/scenario/contract.json": "contract.json",
              "gateway/scenario/agents/diagnose.py": "diagnose.py",
              "gateway/scenario/agents/repair.py": "repair.py",
              "gateway/scenario/agents/preflight.py": "preflight.py", "gateway/vm/guest.py": "guest.py"}
    for source, name in copies.items():
        shutil.copyfile(ROOT / source, app / name)
    shutil.copyfile(HERE / "init.sh", root / "init")
    (root / "init").chmod(0o755)
    shutil.copyfile(HERE / "init_guest.sh", root / "sbin/sc01-init")
    (root / "sbin/sc01-init").chmod(0o755)
    kernel = root / "boot/vmlinuz-virt"
    uid, gid = int(os.environ.get("SUDO_UID", "0")), int(os.environ.get("SUDO_GID", "0"))
    vms = []
    for role, cpu in [("A", 0), ("B", 1)]:
        dest = args.output / ("vm-" + role)
        dest.mkdir()
        (root / "etc/sc01-role").write_text(role + "\n")
        # copyfile writes independent bytes; no reflink, hardlink or qcow backing chain.
        shutil.copyfile(kernel, dest / "kernel")
        image(root, dest / "initramfs.gz")
        disk = dest / "state.raw"
        with disk.open("wb") as stream:
            stream.truncate(256 * 1024 * 1024)
        subprocess.run(["/usr/sbin/mkfs.ext4", "-q", "-F", "-d", str(root), str(disk)], check=True)
        net = ("listen" if role == "A" else "connect") + "=127.0.0.1:" + str(args.port)
        argv = [str(qemu), "-no-user-config", "-nodefaults", "-machine",
                "virt-11.1,memory-backend=ram", "-accel", "tcg,thread=single", "-cpu", "cortex-a57",
                "-smp", "1", "-m", "512M", "-object",
                "memory-backend-ram,id=ram,size=512M,merge=off,prealloc=on,share=off",
                "-display", "none", "-monitor", "none", "-serial", "stdio", "-no-reboot",
                "-qmp", "unix:" + str(dest / "qmp.sock") + ",server=on,wait=off",
                "-kernel", str(dest / "kernel"), "-initrd", str(dest / "initramfs.gz"),
                "-append", "console=ttyAMA0 rdinit=/init panic=-1 quiet",
                "-drive", "file=" + str(disk) + ",format=raw,if=none,id=state",
                "-device", "virtio-blk-device,drive=state", "-netdev", "socket,id=link," + net,
                "-device", "virtio-net-pci,netdev=link,mac=52:54:00:00:00:0" + role.lower().replace("a", "1").replace("b", "2")]
        vms.append({"name": "VM-" + role, "role": "sender+gateway" if role == "A" else "receiver",
                    "cpu_affinity": [cpu], "numa_node": 0, "qemu_argv": argv,
                    "images": {p.name: {"path": str(p), "initial_sha256": sha(p)}
                               for p in [dest / "kernel", dest / "initramfs.gz", disk]}})
        for p in dest.iterdir():
            p.chmod(0o600 if p.name == "state.raw" else 0o444)
            os.chown(p, uid, gid)
        os.chown(dest, uid, gid)
    config = {"schema": "sc01-qemu-pair/1", "accelerator": "tcg", "vms": vms,
              "qemu": {"version": subprocess.check_output([str(qemu), "--version"], text=True).splitlines()[0],
                       "path": str(qemu), "sha256": sha(qemu)},
              "image_lock_sha256": sha(HERE / "image.lock.json"),
              "source_hashes": {rel: sha(ROOT / rel) for rel in list(copies) + ["gateway/vm/init.sh", "gateway/vm/init_guest.sh", "gateway/vm/provision.py"]},
              "host": {"kernel": os.uname().release, "numa": {"0": [0, 1]},
                       "cpu_cache_sharing": {str(p): p.read_text().strip()
                                             for p in Path("/sys/devices/system/cpu/cpu0/cache").glob("*/shared_cpu_list")}},
              "management": "Independent serial pipes and QMP sockets to a trusted host supervisor; never relayed to agents",
              "network": "One QEMU socket link; only VM-A gateway and VM-B trusted receiver service use guest interfaces",
              "limits": ["shared host OS and QEMU trusted", "physical cache/timing effects unresolved",
                         "host services can run on both pinned CPUs", "host NUMA node and storage backend shared",
                         "configuration check is not a complete observation or leakage certificate"]}
    out = args.output / "config.json"
    out.write_text(json.dumps(config, indent=2) + "\n")
    os.chown(out, uid, gid)
    os.chown(args.output, uid, gid)
    shutil.rmtree(root)
    print("Created VM configs; SHA-256", canonical_hash(config))


if __name__ == "__main__":
    main()
