#!/usr/bin/env python3
"""Regenerate canonical status from pinned scenario bundles and theorem registry.

This is a synopsis, not a replacement for historical evidence or a claim of
success in an unattended test. Historical ROADMAP/STACK/HANDOFF remain archival.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SIX = ("threat_coverage", "runtime_correspondence", "environment_boundary",
       "lifetime_and_composition", "usefulness", "independent_review")


def render():
    paths = sorted((ROOT / "scenarios").glob("SC-*/manifest.json"))
    rows = [json.loads(p.read_text()) for p in paths]
    lines = [
        "# Control Stack — canonical status (generated)",
        "",
        "Generated from `scenarios/*/manifest.json` by "
        "`python3 tools/build_status.py`. This does **not** execute Lean or "
        "scenario experiments. A recorded theorem/receipt is not new validation. "
        "**No deployment-assured scenario.**",
        "",
        "| Scenario | Narrow scope | Recorded case status | Unresolved / refuted applicability |",
        "|---|---|---|---|",
    ]
    for m in rows:
        blocked = [k for k in SIX if m["axes"][k]["status"] != "SUPPORTED"]
        blocked_text = ", ".join(f"{k}: {m['axes'][k]['status']}" for k in blocked)
        lines.append(f"| [{m['id']}](scenarios/{m['id']}/result.md) | "
                     f"{m['claim_scope'].replace('|', '/')} | "
                     f"{m['declared_status']} | {blocked_text} |")
    lines += ["", "## Next gates (not executed by this status generator)", "",
              "1. SC-01: owner decision on different VM host or separately frozen "
              "deadline-amendment protocol; historical 0.25-second TCG gate remains failed.",
              "2. SC-01: independent complete receiver-observation and lifetime-lineage "
              "correspondence; single-host cache observation refutes sole-view premise.",
              "3. SC-03: all-destination attribution, permitted-deputy coverage, "
              "and target-workload-matched usefulness.",
              "4. SC-13/27: exclusive dispatch authority, signed source-bound attestation "
              "and independent evidence provenance before broader claims.",
              "5. Explicitly classify adversary models before composing heterogeneous theorems.",
              "",
              "## Source of truth and history", "",
              "- [Theorem registry](THEOREM-REGISTRY.md) — source inventory with "
              "recorded status and unclassified gaps",
              "- [Scenario catalog](SCENARIO-CATALOG.md) — all 28 candidate threats",
              "- [Scenario bundles](scenarios/README.md) — pinned proof/evidence "
              "and six applicability axes",
              "- [Adversary classes](ADVERSARY-CLASSES.md) — quantification boundaries",
              "- [VM historical failure](gateway/vm/STATUS.md) — unchanged evidence",
              "- [Historical roadmap](ROADMAP.md), [STACK](STACK.md), "
              "[session](SESSION.md), and [handoff](HANDOFF.md) — not silently rewritten",
              "",
              "## Reproducibility", "", 
              "```sh",
              "python3 tools/check_scenario.py --all",
              "python3 tools/build_registry.py --check",
              "python3 tools/build_status.py --check",
              "```",
              "",
              "A checker's zero exit indicates pinned-file consistency only; "
              "it is not a safety/usefulness pass and is not a green deployment gate.",
              ""]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    dest = ROOT / "STATUS.md"
    content = render()
    if args.check:
        if not dest.exists() or dest.read_text() != content:
            raise SystemExit("STATUS.md stale: run tools/build_status.py")
    else:
        dest.write_text(content)


if __name__ == "__main__":
    main()
