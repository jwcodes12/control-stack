#!/usr/bin/env python3
"""Read-only SC-01 prospective host capability diagnostic (never runs a guest).

No provisioning, network calls, credentials, side-channel probes, or protocol
amendments. KVM access alone does not establish guest isolation, usefulness,
receiver-observation completeness or authorized hosting.
"""
import fcntl
import json
import os
import platform
import shutil
import stat
import sys
from pathlib import Path


def inspect():
    arch = platform.machine().lower()
    kvm_path = Path("/dev/kvm")
    data = {
        "schema": "sc01-host-capabilities/1",
        "host_arch": arch,
        "cpu_count": os.cpu_count(),
        "kvm_device_exists": kvm_path.exists(),
        "kvm_character_device": False,
        "kvm_api_version": None,
        "kvm_access_error_class": None,
        "qemu_aarch64_available": bool(shutil.which("qemu-system-aarch64")),
        "qemu_x86_64_available": bool(shutil.which("qemu-system-x86_64")),
        "frozen_guest_arch": "aarch64",
        "same_arch_as_frozen_guest": arch in {"aarch64", "arm64"},
        "role": "host capability diagnostic; not proof and not SC-01 usefulness evidence",
    }
    if kvm_path.exists():
        try:
            data["kvm_character_device"] = stat.S_ISCHR(kvm_path.stat().st_mode)
            if data["kvm_character_device"]:
                fd = os.open(kvm_path, os.O_RDWR | os.O_CLOEXEC)
                try:
                    data["kvm_api_version"] = fcntl.ioctl(fd, 0xAE00, 0)
                finally:
                    os.close(fd)
        except (OSError, PermissionError) as exc:
            data["kvm_access_error_class"] = type(exc).__name__
    data["candidate_for_native_guest_acceleration"] = (
        data["same_arch_as_frozen_guest"] and data["kvm_api_version"] == 12)
    return data


if __name__ == "__main__":
    json.dump(inspect(), sys.stdout, sort_keys=True, indent=2)
    print()
