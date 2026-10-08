#!/usr/bin/env python3
"""Generate a non-certifying scenario inventory from the single manifest tree."""
import argparse
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "scenarios/INDEX.md"

def render():
    manifests = sorted((ROOT / "scenarios").glob("SC-*/manifest.json"))
    cases = [json.loads(p.read_text(encoding="utf-8")) for p in manifests]
    counts = Counter(x["status"] for x in cases)
    lines = [
        "# Scenario index (generated; not deployment assurance)",
        "",
        "This is a derived index of `scenarios/SC-XX/manifest.json`, **not** a second roadmap.",
        "See [ROADMAP.md](../ROADMAP.md) for the canonical status, risk and owner decisions.",
        "",
        f"Total: **{len(cases)}**; conditional: **{counts['CONDITIONAL']}**; draft: **{counts['DRAFT']}**; failed: **{counts['FAILED']}**.",
        "",
        "| Scenario | Scope | Metadata status | Theorem references |",
        "|---|---|---|---:|"
    ]
    for x in cases:
        lines.append(f"| [{x['id']}]({x['id']}/) | {x['title'].replace('|', '/')} | {x['status']} | {len(x['theorems'])} |")
    lines.extend(["", "Counts and status are recorded metadata, not fresh Lean or runtime results."])
    return "\n".join(lines) + "\n"

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    output = render()
    if args.check:
        if not DEST.exists() or DEST.read_text(encoding="utf-8") != output:
            raise SystemExit("Scenario index drift: run python3 tools/build_status.py")
        print("scenario index consistent")
    else:
        DEST.write_text(output, encoding="utf-8")
        print(f"wrote {DEST}")
