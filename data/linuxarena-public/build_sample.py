#!/usr/bin/env python3
"""Reviewer-sample builder for the LinuxArena Public Mirror.
Reproduces data/sample.jsonl byte-for-byte from data/*.jsonl. Run from repo root:
    python scripts/build_sample.py
"""
import json, os, sys
from collections import defaultdict

DATA_DIR = "data"
OUT = "data/sample.jsonl"

RUNS = {
    # run_display_name : run_id  (all rows for each)
    "Haiku honest":                            "06f0f3e82bf347d9a1271f806ee2234d",
    "Haiku attack":                            "2b313d861a1c41d4a0f7f28deaccae7a",
    "GPT-5 Nano monitor on Haiku attack":      "41da37d4cecf46e0aa41271d4cb5c800",
    "GPT-5 Nano monitor on straj":             "5990603621e54dc4ac386bb8fa942bca",
    "Opus monitor on straj":                   "fe312f77077f4b919b886059d6d88e98",
    "GPT-5 Nano monitor on Opus honest":       "f25f1eafacd749e89f1736f26d3df751",
    "Opus monitor on Opus honest":             "dfe5b33a58a945f1b02612ca08cbe51a",
}
WANT_RIDS = set(RUNS.values())

bucket = defaultdict(list)  # run_id -> list of (traj_id, line)
for shard in sorted(os.listdir(DATA_DIR)):
    p = os.path.join(DATA_DIR, shard)
    with open(p) as f:
        for line in f:
            try:
                r = json.loads(line)
            except Exception:
                continue
            if r.get("run_id") in WANT_RIDS:
                bucket[r["run_id"]].append((r.get("trajectory_id"), line))
    print(f"scanned {shard}", file=sys.stderr)

with open(OUT, "w") as out:
    counts = []
    # Write in the order RUNS is declared (deterministic README ordering)
    for name, rid in RUNS.items():
        rows = sorted(bucket[rid], key=lambda t: t[0] or "")
        for _, raw in rows:
            out.write(raw)
        counts.append((name, rid, len(rows)))

size = os.path.getsize(OUT)
total = sum(c[2] for c in counts)
print(f"\nTotal rows: {total}")
print(f"File size:  {size:,} bytes  ({size/1e6:.1f} MB, {size/1e9:.2f} GB)")
print()
print("Per-run counts:")
for n, r, c in counts:
    print(f"  {n:<40} | {r} | {c}")

with open("sample_runs.json", "w") as f:
    json.dump([{"name":n,"run_id":r,"count":c} for n,r,c in counts], f, indent=2)
