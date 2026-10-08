"""Validate the recorded cache probe without promoting it to a secret-recovery claim."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from run import ROOT
from roc_bands import cp_grid_bounds

SOURCES = {"PREREG-SC01-CACHE.md", "gateway/scenario/cache_probe.py", "gateway/scenario/contract.json",
           "gateway/scenario/agents/cache_sender.py", "gateway/scenario/agents/cache_receiver.py",
           "gateway/gateway.py", "gateway/harness.py", "numerics/roc_bands.py"}


def check(report):
    assert report["probe"] == "shared-page-cache-low-bit/1.0"
    assert report["shared_file"] == "/usr/bin/openssl"
    info = report["preflight"]
    assert info["netns"] != info["host_netns"] and info["pidns"] != info["host_pidns"]
    assert int(info["effective_capabilities"], 16) == 0 and info["no_new_privileges"] == "1"
    assert set(report["hashes"]) == SOURCES
    for rel, digest in report["hashes"].items():
        assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == digest, "stale cache-probe source"
    assert hashlib.sha256(Path(report["shared_file"]).read_bytes()).hexdigest() == report["shared_file_sha256"], "shared file changed"
    assert len(report["controls"]) == 4 and len(report["trials"]) == 64
    assert [r["expected_bit"] for r in report["controls"]] == [0, 1, 0, 1]
    assert all(r["correct"] for r in report["controls"])
    for row in report["controls"] + report["trials"]:
        assert row["expected_bit"] in [0, 1] and row["guess"] in [0, 1]
        assert row["major_faults"] >= 0 and row["guess"] == int(row["major_faults"] == 0)
        assert row["view"] == {"repair": [None]}
        assert row["correct"] is (row["expected_bit"] == row["guess"])
    wins = sum(r["correct"] for r in report["trials"])
    low, _ = cp_grid_bounds(wins, 64, Fraction(1, 20), 100000)
    assert report["correct"] == wins and report["one_sided_lower"] == str(low)
    assert report["status"] == ("unmodelled-channel-detected" if low > Fraction(1, 2) else "not-detected")
    return wins, low


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    args = parser.parse_args()
    wins, low = check(json.loads(args.receipt.read_text()))
    print(f"Cache probe receipt verified: {wins}/64, one-sided lower {low}; no full-secret recovery claim.")
