#!/usr/bin/env python3
"""Reproducible 187-claim English-to-Lean/manifest/axiom traceability index.

Source fingerprints are full SHA-256; dependency rows originate from Lean's
elaborated Environment via build_lean_dependencies.py, not text grep.
No gate result is promoted to independent or strictly blind verification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs" / "lean-english"
CLAIM = re.compile(r"(?m)^### `([^`\n]+)`[^\n]*$")
SOURCE = re.compile(r"`((?:ControlStack|proofs|ledger)/[^`\n]+\.lean):(\d+)`")
SCENARIO = re.compile(r"SC-\d{2}|DEPLOY")


def parse_blocks() -> list[dict]:
    claims = []
    for part in sorted(DOCS.glob("part-g*.md")):
        text = part.read_text()
        headers = list(CLAIM.finditer(text))
        for i, match in enumerate(headers):
            name = match.group(1)
            first = match.start()
            end = headers[i + 1].start() if i + 1 < len(headers) else len(text)
            # Stop before the next scenario header if the last claim in a section.
            remainder = text[match.end():end]
            heading = re.search(r"(?m)^## (?:Scenario )?(?:SC-\d{2}|DEPLOY)", remainder)
            if heading:
                end = match.end() + heading.start()
            preceding = list(re.finditer(r"(?m)^## [^\n]+", text[:first]))
            scenario_match = SCENARIO.search(preceding[-1].group() if preceding else "")
            scenario = scenario_match.group() if scenario_match else None
            location = SOURCE.search(match.group())
            if not location:
                raise ValueError(f"{part.name}: missing Lean file:line for {name}")
            path, line = location.group(1), int(location.group(2))
            file = ROOT / path
            if not file.is_file():
                raise ValueError(f"missing source file for {name}: {path}")
            source_lines = file.read_text().splitlines()
            if not (1 <= line <= len(source_lines)):
                raise ValueError(f"invalid source line {path}:{line}")
            claims.append({
                "ordinal": len(claims) + 1, "lean": name,
                "scenario": scenario, "english_part": part.relative_to(ROOT).as_posix(),
                "english_block": text[first:end].strip(),
                "source": {"path": path, "line": line,
                           "sha256": hashlib.sha256(file.read_bytes()).hexdigest()},
            })
    if len(claims) != 187:
        raise ValueError(f"expected exactly 187 English claim blocks, got {len(claims)}")
    return claims


def manifests() -> dict:
    return {
        path.parent.name: json.loads(path.read_text())
        for path in sorted((ROOT / "scenarios").glob("SC-*/manifest.json"))
    }


def g0_verdicts() -> dict[str, dict]:
    text = (DOCS / "one-to-one" / "RESULTS.md").read_text()
    rows = {}
    for line in text.splitlines():
        match = re.match(r"^\|\s*(\d+)\s*\|\s*`([^`]+)`\s*\|\s*([^|]+)\|", line)
        if match:
            rows[match.group(2)] = {
                "index": int(match.group(1)), "historical_verdict": match.group(3).strip(),
                "source": "docs/lean-english/one-to-one/RESULTS.md",
                "strictly_blind": False,
                "independent_review": False,
            }
    return rows


def render() -> tuple[str, str]:
    claims = parse_blocks()
    dependency_file = DOCS / "DEPENDENCIES.json"
    if not dependency_file.exists():
        raise RuntimeError(
            "Lean environment dependencies are missing; run build_lean_dependencies.py "
            "with the pinned Lean toolchain first. Do not generate a placeholder."
        )
    deps = json.loads(dependency_file.read_text())
    dep_rows = deps.get("claims", [])
    if len(dep_rows) != len(claims):
        raise ValueError("Lean dependency index not aligned with 187 claims")
    by_scenario, g0 = manifests(), g0_verdicts()
    for claim, dep in zip(claims, dep_rows, strict=True):
        if claim["ordinal"] != dep["ordinal"] or claim["lean"] != dep["lean"]:
            raise ValueError(f"dependency row mismatch at {claim['ordinal']}")
        m = by_scenario.get(claim["scenario"])
        matching = [t for t in m.get("theorems", [])
                    if t.get("name") == claim["lean"]] if m else []
        matching_path = [t for t in matching
                         if t.get("path") == claim["source"]["path"]]
        if len(matching_path) > 1:
            raise ValueError(f"ambiguous scenario manifest theorem: {claim['lean']}")
        pinned = matching_path[0] if matching_path else None
        claim["manifest"] = {
            "path": f"scenarios/{claim['scenario']}/manifest.json" if m else None,
            "scenario_status": m.get("status") if m else "NO_SCENARIO_MANIFEST",
            "theorem_recorded_status": pinned.get("recorded_status") if pinned else "NOT_LISTED",
            "manifest_sha256": pinned.get("sha256") if pinned else None,
            "source_pin_matches": (
                pinned.get("sha256") == claim["source"]["sha256"]
                if pinned else None
            ),
        }
        claim["premises"] = m.get("assumptions", []) if m else []
        claim["evidence"] = m.get("evidence", []) if m else []
        claim["dependencies"] = {
            "direct": dep["direct"], "transitive_project": dep["dependencies"],
            "axioms": dep["axioms"], "standard_axioms_only": dep["axioms_standard"],
            "source": "docs/lean-english/DEPENDENCIES.json",
        }
        short = claim["lean"].rsplit(".", 1)[-1]
        if claim["english_part"].endswith("part-g0.md"):
            history = g0.get(short)
            if history is None:
                raise ValueError(f"no G0 verdict row for {claim['lean']}")
            status = "STALE" if "STALE" in history["historical_verdict"] else "G0 gate-checked verdict (non-blind)"
            claim["one_to_one"] = {"status": status, **history, "verified": False}
        else:
            claim["one_to_one"] = {
                "status": "not checked", "historical_verdict": None,
                "strictly_blind": False, "independent_review": False, "verified": False,
            }
    if sum(c["one_to_one"]["status"] == "not checked" for c in claims) != 161:
        raise ValueError("G1–G7 count must be 161; do not promote an unchecked block")
    machine = json.dumps({
        "method": "English blocks plus full source SHA-256, pinned manifest, Lean environment dependency index",
        "claim_count": 187,
        "independent_human_review": False,
        "strict_blind_g0_verified": False,
        "claims": claims,
    }, indent=2, ensure_ascii=False) + "\n"
    markdown = [
        "# Claim-to-proof traceability — 187 English claims", "",
        "**Model-written, model-reviewed; no independent human review.** "
        "No claim is independently verified one-to-one: historical G0 verdicts are "
        "non-strictly-blind, changed G0 verdicts are STALE and G1–G7 (161 claims) "
        "have never been checked.", "",
        "Generated by tools/build_lean_traceability.py, using the environment-backed "
        "DEPENDENCIES.json. The accompanying JSON holds the **full English block**, "
        "source file/line/SHA-256, recorded manifest status/assumptions/evidence, "
        "Lean dependency and axiom arrays, and G0 freshness.", "",
        "| # | Lean name | Source / SHA-256 prefix | Manifest | Assumptions | Evidence | Axioms | One-to-one |",
        "|---|---|---|---|---:|---:|---|---|",
    ]
    for c in claims:
        src = c["source"]
        ax = ", ".join(c["dependencies"]["axioms"]) or "(none)"
        if not c["dependencies"]["standard_axioms_only"]:
            ax += " **NONSTANDARD**"
        loc = f"{src['path']}:{src['line']} ({src['sha256'][:12]})"
        markdown.append(
            f"| {c['ordinal']} | {c['lean']} | {loc} | "
            f"{c['manifest']['scenario_status']} / "
            f"{c['manifest']['theorem_recorded_status']} | "
            f"{len(c['premises'])} | {len(c['evidence'])} | "
            f"{ax} | {c['one_to_one']['status']} |"
        )
    markdown.extend(["", "**Interpretation:** a SHA-pinned Lean theorem and standard axiom "
                     "footprint do not establish English equivalence, runtime "
                     "faithfulness, complete authority extraction, or human review.", ""])
    return machine, "\n".join(markdown)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    machine, markdown = render()
    outputs = {
        DOCS / "TRACEABILITY.json": machine,
        DOCS / "TRACEABILITY.md": markdown,
    }
    if args.check:
        for path, content in outputs.items():
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f"stale claim traceability artifact: {path}")
        print("claim-to-proof traceability consistent: 187 claims")
    else:
        for path, content in outputs.items():
            path.write_text(content)
        print("generated claim-to-proof traceability: 187 claims")


if __name__ == "__main__":
    main()
