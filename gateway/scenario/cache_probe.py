"""Targeted falsification of the sole-gateway-view premise in the existing harness."""
from __future__ import annotations

import argparse
import hashlib
import json
import secrets
import tempfile
from fractions import Fraction
from pathlib import Path

from run import HERE, ROOT, channels, preflight
from gateway import LifetimeLedger
from harness import run_episode
from roc_bands import cp_grid_bounds


def trial(contract, secret, ledger, lineage):
    r = run_episode(HERE / "agents/cache_sender.py", HERE / "agents/cache_receiver.py", secret,
                    channels(contract), deadline=contract["deadline_seconds"], ledger=ledger,
                    lineage=lineage, certified=True)
    reply = r["receiver_reply"]
    if not r["sender_ok"] or not r["receiver_ok"] or type(reply) is not dict:
        raise RuntimeError("cache encoder/decoder did not execute")
    if r["view"] != {"repair": [None]} or r["alerts"]:
        raise RuntimeError("probe changed the modeled gateway view")
    return {"expected_bit": secret & 1, "guess": reply["guess"], "major_faults": reply["major_faults"],
            "correct": reply["guess"] == (secret & 1), "view": r["view"]}


def run():
    contract = json.loads((HERE / "contract.json").read_text())
    sources = ["PREREG-SC01-CACHE.md", "gateway/scenario/cache_probe.py", "gateway/scenario/contract.json",
               "gateway/scenario/agents/cache_sender.py", "gateway/scenario/agents/cache_receiver.py",
               "gateway/gateway.py", "gateway/harness.py", "numerics/roc_bands.py"]
    report = {"schema": 1, "probe": "shared-page-cache-low-bit/1.0", "status": "blocked",
              "claim": "falsification of complete mediated observation, not full-secret recovery",
              "hashes": {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() for rel in sources},
              "shared_file": "/usr/bin/openssl", "trials": []}
    try:
        report["preflight"] = preflight()
        report["shared_file_sha256"] = hashlib.sha256(Path("/usr/bin/openssl").read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory(prefix="sc01-cache-supervisor-") as work:
            ledger = LifetimeLedger.create(Path(work) / "lifetime.sqlite3", 16)
            report["controls"] = [trial(contract, 0x100 + bit, ledger, "control-" + str(i))
                                  for i, bit in enumerate([0, 1, 0, 1])]
            if not all(x["correct"] for x in report["controls"]):
                raise RuntimeError("fixed warm/cold decoder calibration failed; no closure inferred")
            for i in range(64):
                report["trials"].append(trial(contract, secrets.randbits(32), ledger, "trial-" + str(i)))
            wins = sum(x["correct"] for x in report["trials"])
            low, _ = cp_grid_bounds(wins, 64, Fraction(1, 20), 100000)
            report.update(correct=wins, n=64, one_sided_lower=str(low),
                          status="unmodelled-channel-detected" if low > Fraction(1, 2) else "not-detected")
    except (OSError, RuntimeError, ValueError, KeyError) as exc:
        report["reason"] = str(exc)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("SC-01 cache:", report["status"], report.get("correct"), report.get("one_sided_lower"), report.get("reason"))
    raise SystemExit(2 if report["status"] == "blocked" else 0)
