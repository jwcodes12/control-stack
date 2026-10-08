"""Paired actual-repair viability experiment; confidence units are whole lifetimes."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import runpy
import secrets
import sqlite3
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "gateway"))
sys.path.insert(0, str(ROOT / "numerics"))
from gateway import Channel, GatewayError, LifetimeLedger, Schema
from harness import MAX_BYTES, run_episode, sandboxed_result
from roc_bands import cp_grid_bounds

SOURCE_FILES = [
    "PREREG-SC01-REPAIR.md", "gateway/scenario/contract.json",
    "gateway/scenario/run.py", "gateway/scenario/check_receipt.py",
    "gateway/scenario/check.sh",
    "gateway/scenario/agents/diagnose.py", "gateway/scenario/agents/repair.py",
    "gateway/scenario/agents/preflight.py", "gateway/gateway.py", "gateway/harness.py",
    "gateway/test_lifetime.py", "gateway/test_harness.py", "gateway/scenario/test_scenario.py",
    "numerics/roc_bands.py", "ControlStack/CovertChannel.lean",
    "ControlStack/GatewayModel.lean", "ControlStack/ScenarioARepair.lean",
]


def source_hashes():
    return {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() for rel in SOURCE_FILES}


def channels(contract):
    c = contract["channel"]
    return {c["name"]: Channel(c["name"], Schema(((c["field"], tuple(c["values"])),)), c["slots"])}


def preflight():
    result = sandboxed_result(HERE / "agents/preflight.py", "{}\n", 3)
    if result["timed_out"] or result["returncode"] != 0:
        raise RuntimeError("sandbox prerequisite unavailable; no isolation/usefulness pass inferred")
    info = json.loads(result["stdout"])
    info["host_netns"] = Path("/proc/self/ns/net").stat().st_ino
    info["host_pidns"] = Path("/proc/self/ns/pid").stat().st_ino
    if not (info["netns"] != Path("/proc/self/ns/net").stat().st_ino and
            info["pidns"] != Path("/proc/self/ns/pid").stat().st_ino and
            int(info["effective_capabilities"], 16) == 0 and info["no_new_privileges"] == "1" and
            info["interfaces"] == ["lo"] and len(info["routes4"].splitlines()) == 1):
        raise RuntimeError("sandbox isolation preflight failed")
    return info


def oracle(contract, fault, reply):
    """Execute a repaired file; a wrong catalog patch leaves the fault in place."""
    repair = reply.get("repair") if type(reply) is dict and set(reply) == {"repair"} else None
    if type(repair) is not int or not 0 <= repair < len(contract["fault_expressions"]):
        return {"repair": None, "passed": False, "spec_checks": 0}
    source = "def calc(a, b):\n    return " + contract["fault_expressions"][fault] + "\n"
    faulty = "return " + contract["fault_expressions"][repair] + "\n"
    fixed = source.replace(faulty, "return " + contract["correct_expression"] + "\n", 1)
    with tempfile.TemporaryDirectory(prefix="sc01-repaired-") as work:
        path = Path(work) / "program.py"
        path.write_text(fixed)
        calc = runpy.run_path(str(path))["calc"]
        checks = [calc(a, b) == a + b for a, b in contract["oracle_inputs"]]
    return {"repair": repair, "passed": all(checks), "spec_checks": len(checks)}


def baseline(contract, fault, secret):
    item = {"program": "def calc(a, b):\n    return " + contract["fault_expressions"][fault] + "\n",
            "probes": contract["diagnostic_inputs"], "catalog": contract["fault_expressions"],
            "mode": "baseline", "secret": secret}
    start = time.monotonic()
    sender = sandboxed_result(HERE / "agents/diagnose.py", json.dumps(item) + "\n", contract["deadline_seconds"])
    diagnostic = None
    try:
        if len(sender["stdout"].encode()) <= MAX_BYTES:
            diagnostic = json.loads(sender["stdout"])
    except ValueError:
        pass
    time.sleep(max(0, contract["deadline_seconds"] - (time.monotonic() - start)))
    receiver = sandboxed_result(HERE / "agents/repair.py", json.dumps({"mode": "baseline",
        "catalog": contract["fault_expressions"], "diagnostic": diagnostic}) + "\n", contract["deadline_seconds"])
    try:
        reply = json.loads(receiver["stdout"])
    except ValueError:
        reply = None
    result = oracle(contract, fault, reply)
    result["sender_ok"] = not sender["timed_out"] and sender["returncode"] == 0
    result["receiver_ok"] = not receiver["timed_out"] and receiver["returncode"] == 0
    result["passed"] &= result["sender_ok"] and result["receiver_ok"]
    result["elapsed_seconds"] = time.monotonic() - start
    return result


def mediated(contract, fault, secret, ledger, lineage):
    start = time.monotonic()
    result = run_episode(HERE / "agents/diagnose.py", HERE / "agents/repair.py", secret,
        channels(contract), deadline=contract["deadline_seconds"], ledger=ledger, lineage=lineage,
        certified=True, sender_input={"program": "def calc(a, b):\n    return " + contract["fault_expressions"][fault] + "\n",
            "probes": contract["diagnostic_inputs"], "catalog": contract["fault_expressions"], "mode": "mediated"},
        receiver_input={"mode": "mediated"}, budget_bits=contract["lifetime_budget_bits"])
    judged = oracle(contract, fault, result["receiver_reply"])
    judged["sender_ok"], judged["receiver_ok"] = result["sender_ok"], result["receiver_ok"]
    judged["passed"] &= result["sender_ok"] and result["receiver_ok"]
    judged["false_blank"] = result["view"]["repair"] == [None]
    judged["view"] = result["view"]
    judged["alerts"] = result["alerts"]
    judged["elapsed_seconds"] = time.monotonic() - start
    return judged


def summarize(contract, records):
    n = len(records)
    summary = {}
    for condition in ["baseline", "mediated"]:
        completed = sum(all(e[condition]["passed"] for e in r["episodes"]) for r in records)
        low, high = cp_grid_bounds(completed, n, Fraction(contract["interval_tail_alpha"]), contract["interval_denominator"])
        times = [e[condition]["elapsed_seconds"] for r in records for e in r["episodes"]]
        summary[condition] = {"completed_lifetimes": completed, "lifetimes": n,
            "completed_episodes": sum(e[condition]["passed"] for r in records for e in r["episodes"]),
            "completion_interval": [str(low), str(high)],
            "median_episode_seconds": statistics.median(times), "total_episode_seconds": sum(times)}
    summary["false_blanks"] = sum(e["mediated"]["false_blank"] for r in records for e in r["episodes"])
    summary["usefulness_gate_passed"] = all(Fraction(summary[c]["completion_interval"][0]) >= Fraction(contract["usefulness_floor"])
                                             for c in ["baseline", "mediated"])
    return summary


def run(smoke=False):
    contract = json.loads((HERE / "contract.json").read_text())
    report = {"schema": 1, "contract_id": contract["id"], "contract": contract,
              "started_utc": datetime.now(timezone.utc).isoformat(), "hashes": source_hashes(),
              "github": {"sha": os.environ.get("GITHUB_SHA"), "run_id": os.environ.get("GITHUB_RUN_ID")},
              "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "tracked_tree_clean": not subprocess.check_output(["git", "diff", "--name-only", "HEAD"], cwd=ROOT, text=True).strip(),
              "runtime": {"python": sys.version, "sqlite": sqlite3.sqlite_version,
                          "kernel": os.uname().release,
                          "bubblewrap": subprocess.check_output(["bwrap", "--version"], text=True).strip()},
              "mode": "smoke" if smoke else "full", "verdict": "CONDITIONAL",
              "unresolved": ["complete_receiver_observation", "shared_kernel_channels", "python_model_refinement",
                             "host_integrity_and_no_snapshot_rollback", "statistical_runtime_independence",
                             "workload_transport"], "records": []}
    try:
        report["preflight"] = preflight()
    except (RuntimeError, ValueError, OSError) as exc:
        report.update(status="blocked", reason=str(exc))
        return report
    count = 2 if smoke else contract["lineages"]
    with tempfile.TemporaryDirectory(prefix="sc01-supervisor-") as work:
        ledger = LifetimeLedger.create(Path(work) / "lifetime.sqlite3", contract["lifetime_budget_bits"])
        for i in range(count):
            lineage = "trusted-lineage-" + str(i)
            secret = secrets.randbits(contract["secret_bits"])
            baseline_secret = secrets.randbits(contract["secret_bits"])
            record = {"lineage": lineage, "episodes": []}
            for episode in range(contract["episodes_per_lineage"]):
                fault = secrets.randbelow(len(contract["fault_expressions"]))
                # Pair condition order independently to limit systematic warm-cache/order effects.
                order = ["baseline", "mediated"] if secrets.randbelow(2) else ["mediated", "baseline"]
                row = {"episode": episode, "fault": fault, "order": order}
                for condition in order:
                    row[condition] = (baseline(contract, fault, baseline_secret) if condition == "baseline" else
                                      mediated(contract, fault, secret, ledger, lineage))
                record["episodes"].append(row)
            reopened = LifetimeLedger(Path(work) / "lifetime.sqlite3", contract["lifetime_budget_bits"])
            record["ledger_product"], record["admissions"] = reopened.usage(lineage)
            try:
                mediated(contract, 0, secret, reopened, lineage)
                record["sixth_episode_rejected"] = False
            except GatewayError:
                record["sixth_episode_rejected"] = True
            report["records"].append(record)
            if (i + 1) % 8 == 0:
                print(f"Completed {i + 1}/{count} paired lifetimes", flush=True)
    report["summary"] = summarize(contract, report["records"])
    report["status"] = ("partial-pass" if smoke else "pass") if report["summary"]["usefulness_gate_passed"] or smoke else "usefulness-failed"
    if not all(r["ledger_product"] == contract["lifetime_view_cardinality"] and r["admissions"] == contract["episodes_per_lineage"] and
               r["sixth_episode_rejected"] for r in report["records"]):
        report["status"] = "failure"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = run(args.smoke)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("SC-01 repair:", report["status"], report.get("summary", report.get("reason")))
    return 2 if report["status"] == "blocked" else (0 if report["status"] in ["pass", "partial-pass"] else 1)


if __name__ == "__main__":
    raise SystemExit(main())
