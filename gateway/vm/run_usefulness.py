#!/usr/bin/env python3
"""Replay the frozen SC-01 paired usefulness gate in the QEMU pair; no channel probes."""
from __future__ import annotations

import argparse
import json
import secrets
import sqlite3
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from check_isolation import check as isolation_check
from pair import Pair
from provision import canonical_hash, sha

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "gateway/scenario"))
import run as scenario

VM_SOURCES = ["gateway/vm/run_usefulness.py", "gateway/vm/check_usefulness.py",
              "gateway/vm/check_isolation.py", "gateway/vm/pair.py", "gateway/vm/provision.py",
              "gateway/vm/guest.py", "gateway/vm/init.sh", "gateway/vm/init_guest.sh",
              "gateway/vm/image.lock.json"]


def vm_hashes():
    return {rel: sha(ROOT / rel) for rel in VM_SOURCES}


def run(config_path, checkpoint):
    config = json.loads(config_path.read_text())
    isolation_check(config, files=True)
    contract = json.loads((ROOT / "gateway/scenario/contract.json").read_text())
    for rel, digest in config["source_hashes"].items():
        if sha(ROOT / rel) != digest:
            raise RuntimeError("VM image source changed: " + rel)
    report = {"schema": "sc01-vm-usefulness/1", "contract_id": contract["id"], "contract": contract,
              "started_utc": datetime.now(timezone.utc).isoformat(), "hashes": scenario.source_hashes(),
              "vm_hashes": vm_hashes(), "config_hash": canonical_hash(config), "config": config,
              "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "tracked_tree_clean": not subprocess.check_output(["git", "diff", "--name-only", "HEAD"], cwd=ROOT, text=True).strip(),
              "runtime": {"host_python": sys.version, "host_sqlite": sqlite3.sqlite_version},
              "mode": "full", "verdict": "CONDITIONAL", "records": [],
              "unresolved": ["complete_receiver_observation", "shared_kernel_channels", "python_model_refinement",
                             "host_integrity_and_no_snapshot_rollback", "statistical_runtime_independence",
                             "workload_transport", "qemu_and_guest_supervisor_integrity",
                             "physical_cache_and_timing_channels", "fixed_five_episode_schedule_correspondence"],
              "evidence_scope": "paired usefulness replay only; distinct from single-host receipts; no channel experiment",
              "status": "running"}
    checkpoint.write_text(json.dumps(report, indent=2) + "\n")
    with Pair(config_path) as pair:
        report["vm_start"] = pair.receipt()
        isolation_check(config, report["vm_start"], files=True)
        report["preflight"] = pair.vms[0].ready["agent"]
        sender = pair.vms[0]
        report["transport_health"] = sender.request({"id": "health", "op": "health"})
        sender.request({"id": "start", "op": "start", "run_id": secrets.token_hex(16)})
        for i in range(contract["lineages"]):
            lineage = "vm-lineage-" + str(i)
            secret, baseline_secret = secrets.randbits(contract["secret_bits"]), secrets.randbits(contract["secret_bits"])
            record = {"lineage": lineage, "episodes": []}
            for episode in range(contract["episodes_per_lineage"]):
                fault = secrets.randbelow(len(contract["fault_expressions"]))
                order = ["baseline", "mediated"] if secrets.randbelow(2) else ["mediated", "baseline"]
                row = {"episode": episode, "fault": fault, "order": order}
                for condition in order:
                    result = sender.request({"id": f"{i}:{episode}:{condition}", "op": "episode",
                        "condition": condition, "fault": fault, "lineage": lineage,
                        "secret": baseline_secret if condition == "baseline" else secret})
                    judged = scenario.oracle(contract, fault, result.pop("receiver_reply"))
                    judged.update(result)
                    judged["passed"] &= judged["sender_ok"] and judged["receiver_ok"]
                    row[condition] = judged
                record["episodes"].append(row)
            record.update(sender.request({"id": "usage:" + str(i), "op": "usage", "lineage": lineage}))
            report["records"].append(record)
            checkpoint.write_text(json.dumps(report, indent=2) + "\n")
            if (i + 1) % 8 == 0:
                print(f"Completed {i + 1}/{contract['lineages']} paired VM lifetimes", flush=True)
        report["vm_end"] = pair.receipt()
        isolation_check(config, report["vm_end"], files=True)
    report["summary"] = scenario.summarize(contract, report["records"])
    report["status"] = "pass" if report["summary"]["usefulness_gate_passed"] else "usefulness-failed"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("refusing to overwrite a receipt")
    try:
        report = run(args.config, args.output)
    except Exception as exc:
        report = json.loads(args.output.read_text()) if args.output.exists() else {
            "schema": "sc01-vm-usefulness/1", "mode": "full", "records": []}
        report.update(status="blocked", error_type=type(exc).__name__, reason=str(exc),
                      finished_utc=datetime.now(timezone.utc).isoformat())
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print("VM usefulness blocked:", report["reason"], file=sys.stderr)
        return 2
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("VM usefulness", report["status"], json.dumps(report["summary"], sort_keys=True))
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
