#!/usr/bin/env python3
"""Scenario checker: --lint checks metadata only; --verify fails closed.
Manifest-supplied commands are never executed. No automatic assurance promotion.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AXES = ("proof", "evidence", "applicability", "usefulness")
FAMILIES = {f"F{i}" for i in range(1, 9)}
CLASSES = {"non-adaptive", "adaptive-feedback", "shared-seed",
           "shared-seed-side-observing", "multi-agent-persistent", "unspecified"}
STATUSES = {"historical", "unresolved", "failed", "not_applicable"}
ASSUMPTION_STATUSES = {"unresolved", "assumed", "tested", "refuted"}


class Invalid(ValueError):
    pass


def pairs_to_object(pairs):
    d = {}
    for key, value in pairs:
        if key in d:
            raise Invalid(f"duplicate key: {key}")
        d[key] = value
    return d


def path_at_root(relative, nullable=False):
    if nullable and relative is None:
        return None
    if not isinstance(relative, str) or not relative or relative.startswith("/"):
        raise Invalid(f"bad path: {relative}")
    p = Path(relative)
    if ".." in p.parts or p.as_posix() != relative:
        raise Invalid(f"unsafe path: {relative}")
    resolved = (ROOT / p).resolve()
    if not resolved.is_relative_to(ROOT.resolve()) or not resolved.is_file():
        raise Invalid(f"missing/outside file: {relative}")
    return resolved


def fields(obj, keys, label):
    if not isinstance(obj, dict) or not set(keys).issubset(obj):
        raise Invalid(f"{label}: missing required keys: {set(keys) - set(obj) if isinstance(obj, dict) else keys}")
    return obj


def text(value, label):
    if not isinstance(value, str) or not value.strip():
        raise Invalid(f"{label}: empty or invalid string")


def load_scenario(directory):
    directory = Path(directory).resolve()
    if not directory.is_relative_to((ROOT / "scenarios").resolve()) or not re.fullmatch(r"SC-\d\d", directory.name):
        raise Invalid("scenario directory outside scenarios/SC-XX")
    path = directory / "scenario.json"
    if path.stat().st_size > 512000:
        raise Invalid("oversized scenario file")
    d = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs_to_object)
    fields(d, ("schema_version", "id", "title", "lifecycle", "families", "threat",
               "formal", "policy", "evidence", "axes", "assumptions",
               "falsification", "review"), "scenario")
    if d["schema_version"] != 1 or d["id"] != directory.name or d["lifecycle"] not in {"draft", "active"}:
        raise Invalid("schema version, ID, or lifecycle invalid")
    text(d["title"], "title")
    if not isinstance(d["families"], list) or not d["families"] or not set(d["families"]) <= FAMILIES:
        raise Invalid("missing or invalid families")
    threat = fields(d["threat"], ("bad_event", "attacker_controls", "protected_assets",
                                    "runtime_boundary", "horizon", "permitted_actions",
                                    "forbidden_actions"), "threat")
    for k in ("bad_event", "runtime_boundary", "horizon", "permitted_actions", "forbidden_actions"):
        text(threat[k], "threat." + k)
    for k in ("attacker_controls", "protected_assets"):
        if not isinstance(threat[k], list) or not threat[k] or any(not isinstance(x, str) or not x.strip() for x in threat[k]):
            raise Invalid("threat." + k + ": nonempty string list required")
    formal = fields(d["formal"], ("claim", "source", "adversary_class", "premises", "necessity_witness"), "formal")
    for k in ("claim", "premises", "necessity_witness"):
        text(formal[k], "formal." + k)
    if formal["adversary_class"] not in CLASSES:
        raise Invalid("adversary class unspecified by vocabulary")
    path_at_root(formal["source"], nullable=True)
    policy = fields(d["policy"], ("description", "source"), "policy")
    text(policy["description"], "policy.description")
    path_at_root(policy["source"], nullable=True)
    ev = fields(d["evidence"], ("source_manifest", "artifacts", "hashes", "runner"), "evidence")
    path_at_root(ev["source_manifest"], nullable=True)
    if ev["runner"] not in {"none", "sc01-legacy"} or (ev["runner"] == "sc01-legacy" and d["id"] != "SC-01"):
        raise Invalid("non-allowlisted runner")
    if not isinstance(ev["artifacts"], list) or not isinstance(ev["hashes"], dict):
        raise Invalid("evidence paths/hashes malformed")
    for p in ev["artifacts"]:
        path_at_root(p)
    for p, digest in ev["hashes"].items():
        path_at_root(p)
        if not re.fullmatch("[0-9a-f]{64}", digest):
            raise Invalid("bad SHA256: " + p)
    axes = d["axes"]
    if not isinstance(axes, dict) or set(axes) != set(AXES):
        raise Invalid("all four separate axes required")
    for a in AXES:
        fields(axes[a], ("status", "note"), "axis." + a)
        if axes[a]["status"] not in STATUSES:
            raise Invalid("invalid/promoted axis status: " + a)
        text(axes[a]["note"], "axis." + a + ".note")
    items = d["assumptions"]
    if not isinstance(items, list) or set(x.get("axis") for x in items if isinstance(x, dict)) != set(AXES):
        raise Invalid("each axis needs explicit assumptions")
    seen = set()
    for a in items:
        fields(a, ("id", "axis", "status", "detail"), "assumption")
        text(a["id"], "assumption.id")
        text(a["detail"], "assumption.detail")
        if a["axis"] not in AXES or a["status"] not in ASSUMPTION_STATUSES or a["id"] in seen:
            raise Invalid("bad/duplicate assumption")
        seen.add(a["id"])
    if not isinstance(d["falsification"], list) or not d["falsification"]:
        raise Invalid("missing falsification conditions")
    for f in d["falsification"]:
        text(f, "falsification")
    fields(d["review"], ("decision", "notes"), "review")
    if d["review"]["decision"] != "pending":
        raise Invalid("review promotion not supported by metadata")
    text(d["review"]["notes"], "review.notes")
    for name in ("claim.md", "correspondence.md", "result.md"):
        if not (directory / name).is_file():
            raise Invalid("missing " + name)
    if d["lifecycle"] == "active" and not (directory / "tests" / "README.md").is_file():
        raise Invalid("active scenario lacks tests/README.md")
    return d


def inspect(folder, verify):
    d = load_scenario(folder)
    result = dict(scenario=d["id"], structure="VALID", lifecycle=d["lifecycle"],
                  proof="NOT_EXECUTED", evidence="NOT_EXECUTED",
                  applicability=d["axes"]["applicability"]["status"].upper(),
                  usefulness=d["axes"]["usefulness"]["status"].upper(),
                  blockers=[a["id"] for a in d["assumptions"]
                            if a["status"] in {"unresolved", "assumed", "refuted"}],
                  verdict="NOT_ASSURED", errors=[])
    if not verify:
        return result
    for rel, digest in d["evidence"]["hashes"].items():
        got = hashlib.sha256(path_at_root(rel).read_bytes()).hexdigest()
        if digest != got:
            result["errors"].append("hash mismatch: " + rel)
    if d["evidence"]["hashes"] and not result["errors"]:
        result["evidence"] = "HASHES_MATCH_ONLY"
    if d["evidence"]["runner"] == "sc01-legacy" and not result["errors"]:
        try:
            cmd = subprocess.run([sys.executable, "tools/check_sc01_case.py"],
                                 cwd=ROOT, capture_output=True, text=True, timeout=7200)
            if cmd.returncode:
                result["errors"].append("SC-01 legacy verifier failed: " + (cmd.stdout + cmd.stderr)[-1000:])
                result["proof"] = "FAILED"
            else:
                result["proof"] = "LEGACY_CHECKS_PASSED"
                if "HYPOTHESIS_REFUTED" in cmd.stdout:
                    result["applicability"] = "REFUTED_IN_TESTED_HARNESS"
        except subprocess.TimeoutExpired:
            result["errors"].append("SC-01 legacy verifier timed out")
    result["verdict"] = ("INVALID" if result["errors"] else
                         "BLOCKED" if result["usefulness"] == "FAILED" or "REFUTED" in result["applicability"]
                         else "CONDITIONAL")
    return result


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("scenario", nargs="?")
    ap.add_argument("--all", action="store_true")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--lint", action="store_true")
    mode.add_argument("--verify", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    if args.all == bool(args.scenario):
        ap.error("provide exactly one scenario or --all")
    folders = sorted((ROOT / "scenarios").glob("SC-*")) if args.all else [
        ROOT / "scenarios" / args.scenario if re.fullmatch(r"SC-\d\d", args.scenario)
        else Path(args.scenario)]
    results = []
    for folder in folders:
        try:
            results.append(inspect(folder, verify=args.verify))
        except (Invalid, OSError, ValueError) as exc:
            results.append(dict(scenario=Path(folder).name, structure="INVALID", verdict="INVALID", errors=[str(exc)]))
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        for r in results:
            print(f"{r['scenario']}: {r['verdict']} | structure={r['structure']} "
                  f"proof={r.get('proof', 'N/A')} evidence={r.get('evidence', 'N/A')} "
                  f"applicability={r.get('applicability', 'N/A')} usefulness={r.get('usefulness', 'N/A')}")
            for e in r.get("errors", []):
                print("  ERROR: " + e)
            for a in r.get("blockers", []):
                print("  BLOCKER: " + a)
    if any(r["verdict"] == "INVALID" for r in results):
        return 2
    if args.verify:
        return 3  # never auto-promote model proof + hashes to deployment assurance
    return 0


if __name__ == "__main__":
    sys.exit(main())
