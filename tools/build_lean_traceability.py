#!/usr/bin/env python3
"""Generate claim -> English, Lean source, manifest, evidence, and environment traceability.

Fail closed if the elaborated Lean dependency inventory is absent/incomplete.
A recorded kernel check is NOT a blind, independent English-fidelity result.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARTS = ROOT / "docs" / "lean-english"
OUTPUT_MD = PARTS / "TRACEABILITY.md"
OUTPUT_JSON = PARTS / "TRACEABILITY.json"

HEAD = re.compile(
    r"(?m)^### \x60(?P<lean>ControlStack\.[^\x60]+)\x60"
    r"\s+—\s+\x60(?P<file>[^:\x60]+):(?P<line>\d+)\x60"
)
G0_RESULT = re.compile(
    r"(?m)^\|\s*(?P<id>\d+)\s*\|\s*\x60(?P<name>[^\x60]+)\x60"
    r"\s*\|\s*(?P<verdict>[^|]+)\|"
)
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


def markdown_escape(value: object) -> str:
    return str(value).replace("|", "/").replace("\n", " ").strip()


def english_claims() -> list[dict]:
    results: list[dict] = []
    for path in sorted(PARTS.glob("part-g[0-7].md")):
        text = path.read_text()
        found = list(HEAD.finditer(text))
        for j, match in enumerate(found):
            # The full English block stops at the next claim or major section,
            # whichever comes first. All content remains byte-for-byte derived.
            end = found[j+1].start() if j+1 < len(found) else len(text)
            section = text[match.end():end]
            heading = re.search(r"(?m)^## (?!#)", section)
            if heading:
                section = section[:heading.start()]
            raw = text[match.start():match.end()] + section
            says = re.search(r"(?m)^-\s+\*\*Says[^*]*\*\*\s*(.*)$", raw)
            file_path = match.group("file")
            absolute = ROOT / file_path
            if not absolute.is_file() or not absolute.resolve().is_relative_to(ROOT):
                raise ValueError(f"invalid or missing Lean source file: {file_path}")
            src = absolute.read_bytes()
            line = int(match.group("line"))
            if not (1 <= line <= len(src.splitlines())):
                raise ValueError(f"bad English source location: {file_path}:{line}")
            results.append({
                "ordinal": len(results)+1,
                "english_source": path.relative_to(ROOT).as_posix(),
                "english_block": raw.strip(),
                "english_says": says.group(1).strip() if says else "",
                "lean": match.group("lean"),
                "lean_file": file_path,
                "lean_line": line,
                "lean_file_sha256": hashlib.sha256(src).hexdigest(),
                "group": path.stem.removeprefix("part-").upper(),
            })
    if len(results) != 187:
        raise ValueError(f"expected 187 English blocks; got {len(results)}")
    return results


def manifests() -> dict[str, list[dict]]:
    known: dict[str, list[dict]] = {}
    for path in sorted((ROOT / "scenarios").glob("SC-*/manifest.json")):
        obj = json.loads(path.read_text())
        if not isinstance(obj.get("theorems"), list):
            raise ValueError(f"missing manifest theorem list in {path}")
        for theorem in obj["theorems"]:
            if not isinstance(theorem, dict):
                raise ValueError(f"bad theorem manifest entry in {path}")
            name = theorem.get("name")
            if not name:
                raise ValueError(f"unnamed manifest theorem in {path}")
            known.setdefault(name, []).append({
                "id": obj["id"], "manifest": path.relative_to(ROOT).as_posix(),
                "scenario_status": obj["status"],
                "theorem_recorded_status": theorem.get("recorded_status"),
                "manifest_theorem_file": theorem.get("path"),
                "manifest_theorem_sha256": theorem.get("sha256"),
                "assumptions": obj.get("assumptions", []),
                "evidence": obj.get("evidence", []),
            })
    return known


def g0_verdicts() -> dict[int, dict]:
    results_file = PARTS / "one-to-one" / "RESULTS.md"
    text = results_file.read_text()
    found = {}
    for match in G0_RESULT.finditer(text):
        ordinal = int(match.group("id"))
        found[ordinal] = {"name": match.group("name"),
                          "verdict": match.group("verdict").strip(),
                          "results_source": results_file.relative_to(ROOT).as_posix()}
    if set(found) != set(range(1, 27)):
        raise ValueError("G0 has missing/duplicate numbered comparison result rows")
    return found


def dependencies() -> dict[int, dict]:
    path = PARTS / "DEPENDENCIES.json"
    if not path.exists():
        raise ValueError("DEPENDENCIES.json missing; generate from Lean environment first")
    obj = json.loads(path.read_text())
    if obj.get("claim_count") != 187 or len(obj.get("claims", [])) != 187:
        raise ValueError("environment dependency inventory not 187 rows")
    result = {}
    for row in obj["claims"]:
        if row["ordinal"] in result:
            raise ValueError("duplicate environment dependency ordinal")
        if not {"lean", "direct", "dependencies", "axioms", "axioms_standard"} <= row.keys():
            raise ValueError("missing environment dependency fields")
        if not isinstance(row["lean"], str) or not row["lean"].startswith("ControlStack."):
            raise ValueError("invalid elaborated Lean declaration name")
        for field in ("direct", "dependencies", "axioms"):
            values = row[field]
            if (not isinstance(values, list) or
                    any(not isinstance(x, str) for x in values) or
                    values != sorted(set(values))):
                raise ValueError(f"invalid/unsorted dependency field {field}")
        if not set(row["direct"]) <= set(row["dependencies"]):
            raise ValueError("missing direct declaration from transitive closure")
        if not isinstance(row["axioms_standard"], bool) or row["axioms_standard"] != (set(row["axioms"]) <= STANDARD):
            raise ValueError("axiom verdict mismatch")
        if not row["axioms_standard"]:
            raise ValueError("nonstandard Lean axiom footprint in index")
        result[row["ordinal"]] = row
    if set(result) != set(range(1, 188)):
        raise ValueError("missing dependency rows")
    return result


def build() -> tuple[str, str]:
    rows = english_claims()
    index = manifests()
    verdicts = g0_verdicts()
    dep = dependencies()
    for row in rows:
        ordinal = row["ordinal"]
        item = dep[ordinal]
        if item["lean"] != row["lean"]:
            raise ValueError(f"dependency identity mismatch on claim {ordinal}")
        row["dependency_row"] = item
        matches = index.get(row["lean"], [])
        # Manifests can repeat a theorem across multiple scenarios. Retain all.
        for m in matches:
            if m["manifest_theorem_file"] == row["lean_file"]:
                sha = m.get("manifest_theorem_sha256")
                if sha and sha != row["lean_file_sha256"]:
                    raise ValueError(f"manifest source SHA changed: {row['lean']}")
        row["scenario_manifests"] = matches
        if ordinal <= 26:
            verdict = verdicts[ordinal]
            if verdict["name"] != row["lean"].rsplit(".", 1)[-1]:
                raise ValueError(f"G0 row mismatch: {ordinal}")
            row["one_to_one"] = {
                "status": "STALE" if "STALE" in verdict["verdict"].upper()
                           else "G0 gate-checked verdict (NOT strictly blind)",
                "original_verdict": verdict["verdict"],
                "source": verdict["results_source"],
                "independently_verified": False,
                "strictly_blind": False,
            }
        else:
            row["one_to_one"] = {
                "status": "not checked", "original_verdict": None,
                "source": None, "independently_verified": False,
                "strictly_blind": False,
            }
        row["verified"] = False  # No strictly-blind result is available.
    payload = {
        "claim_count": 187,
        "generated_by": "tools/build_lean_traceability.py",
        "verification_policy": "No claim marked verified without gate-passing strictly-blind comparison",
        "independent_human_review": False,
        "claims": rows,
    }
    machine = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    human = [
        "# Claim-to-proof traceability (187 English headlines)", "",
        "**Model-written and model-reviewed. No independent human review.**",
        "**No English claim in this index is independently or strictly-blind verified.**",
        "A historical G0 gate-checked verdict is not a blind verification;",
        "the 161 G1–G7 claims have never been checked one-to-one.", "",
        "The SHA-256 refers to the current source-file bytes, not a deployment artifact.",
        "Manifest status and recorded kernel checks are historically scoped and do not",
        "close environmental/runtime premises.", "",
        "| # | Lean declaration | English | Source SHA-256 | Scenario status | Fidelity | Standard axioms |",
        "|---|---|---|---|---|---|---|",
    ]
    for row in rows:
        m = row["scenario_manifests"]
        scopes = ", ".join(f"{x['id']}:{x['scenario_status']}" for x in m) or "no scenario theorem mapping"
        human.append(
            f"| {row['ordinal']} | {markdown_escape(row['lean'])} | "
            f"{markdown_escape(row['english_source'])} | "
            f"{row['lean_file_sha256'][:12]} | {markdown_escape(scopes)} | "
            f"{markdown_escape(row['one_to_one']['status'])} | "
            f"{'yes' if row['dependency_row']['axioms_standard'] else 'NO'} |")
    for row in rows:
        human.extend([
            "", f"## {row['ordinal']}. {row['lean']}", "",
            f"Lean: {row['lean_file']}:{row['lean_line']} "
            f"(SHA-256 {row['lean_file_sha256']})", "",
            f"One-to-one: {row['one_to_one']['status']} "
            f"({row['one_to_one']['original_verdict'] or 'not checked'})", "",
            "### Original English block", "",
            row["english_block"], "", "### Scenario manifest premises and evidence", "",
        ])
        for scope in row["scenario_manifests"]:
            human.append(f"- {scope['id']} ({scope['scenario_status']}); manifest: {scope['manifest']}")
            human.append(f"  - theorem recorded status: {scope['theorem_recorded_status']}")
            for assumption in scope["assumptions"]:
                human.append(f"  - premise: {assumption.get('id', '?')} — "
                             f"{markdown_escape(assumption.get('text', ''))}")
            for evidence in scope["evidence"]:
                human.append(f"  - evidence: {evidence.get('path', '?')} "
                             f"(SHA-256 {evidence.get('sha256') or 'unbound'})")
        if not row["scenario_manifests"]:
            human.append("No matching named scenario theorem in the current manifest collection.")
        item = row["dependency_row"]
        human.extend([
            "", "### Elaborated Lean environment", "",
            f"- Direct project dependencies: {', '.join(item['direct']) or '(none)'}",
            f"- Transitive project dependencies: {', '.join(item['dependencies']) or '(none)'}",
            f"- Axioms: {', '.join(item['axioms']) or '(none)'}",
            "",
        ])
    return machine, "\n".join(human)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    p.add_argument("--emit-bootstrap", action="store_true")
    args = p.parse_args()
    machine, human = build()
    expected = {OUTPUT_JSON: machine, OUTPUT_MD: human}
    if args.check:
        for path, data in expected.items():
            if not path.exists() or path.read_text() != data:
                raise SystemExit(f"stale or absent traceability artifact: {path}")
        print("traceability artifacts consistent: 187 claims")
    else:
        for path, data in expected.items():
            path.write_text(data)
        print("wrote 187-claim traceability artifacts")
    if args.emit_bootstrap:
        # Bootstrap transports generated bytes after a pinned GitHub Actions run.
        # It is not a substitute for --check or independent review.
        payload = json.dumps({"json": machine, "md": human},
                             separators=(",", ":"), ensure_ascii=True)
        for i in range(0, len(payload), 12000):
            print(f"CSTRACECHUNK:{i:08d}:{payload[i:i+12000]}")


if __name__ == "__main__":
    main()
