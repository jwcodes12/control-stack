#!/usr/bin/env python3
"""Verify VM/source bindings plus the original frozen SC-01 usefulness gate."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from check_isolation import check as isolation_check
from provision import canonical_hash, sha
from run_usefulness import ROOT, scenario, vm_hashes

sys.path.insert(0, str(ROOT / "gateway/scenario"))
import check_receipt as original_check


def check(report):
    if report["schema"] != "sc01-vm-usefulness/1" or report["mode"] != "full":
        raise ValueError("wrong runtime or incomplete receipt")
    if report.get("transport_health") != {"infrastructure_health": True}:
        raise ValueError("trusted transport health check missing")
    if report["vm_hashes"] != vm_hashes():
        raise ValueError("stale VM runner/checker source binding")
    config = report["config"]
    if report["config_hash"] != canonical_hash(config):
        raise ValueError("VM config hash differs")
    for rel, digest in config["source_hashes"].items():
        if sha(ROOT / rel) != digest:
            raise ValueError("guest source differs: " + rel)
    if sha(ROOT / "gateway/vm/image.lock.json") != config["image_lock_sha256"]:
        raise ValueError("image lock differs")
    for key in ["vm_start", "vm_end"]:
        isolation_check(config, report[key])
    for name in ["VM-A", "VM-B"]:
        before, after = report["vm_start"]["live"][name], report["vm_end"]["live"][name]
        if before["pid"] != after["pid"] or before["guest"]["boot_id"] != after["guest"]["boot_id"]:
            raise ValueError("VM restarted within the replay")
    if report["preflight"] != report["vm_start"]["live"]["VM-A"]["guest"]["agent"]:
        raise ValueError("wrong preflight binding")
    required = {"qemu_and_guest_supervisor_integrity", "physical_cache_and_timing_channels",
                "fixed_five_episode_schedule_correspondence"}
    if not required <= set(report["unresolved"]):
        raise ValueError("VM observation assumption removed")
    # Reuse its oracle, 64 lifetimes, five views, ledger, paired conditions,
    # 90% floor and simultaneous exact-rational confidence calculations.
    return original_check.check(report)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    args = parser.parse_args()
    summary = check(json.loads(args.receipt.read_text()))
    print("VM usefulness receipt verified; CONDITIONAL;", json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
