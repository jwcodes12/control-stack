#!/usr/bin/env python3
"""Validate scenario bundles without running experiments or promoting assurance.

Default: validate schema, evidence digests, theorem source digests and references.
--verify-proofs: additionally ask pinned Lake/Lean to replay the checked theorem
imports and inspect #print axioms output (no runtime scenario tests).
--require-assured: exit nonzero unless every applicability axis is supported,
proofs were checked *this invocation*, and no refuted/assumed premise remains.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AXES = ("threat_coverage", "runtime_correspondence", "environment_boundary",
        "lifetime_and_composition", "usefulness", "independent_review")
STATES = {"SUPPORTED", "ASSUMED", "UNRESOLVED", "REFUTED", "NOT_APPLICABLE"}
CLASSES = {"NON_ADAPTIVE", "ADAPTIVE_FEEDBACK", "SHARED_SEED",
           "SIDE_OBSERVING", "CONTENT_ADAPTIVE", "TRACE_ARBITRARY",
           "UNKNOWN"}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SHA = re.compile(r"[0-9a-f]{64}\Z")


class InvalidCase(Exception):
    pass


def require(cond, message):
    if not cond:
        raise InvalidCase(message)


def source_file(path):
    require(isinstance(path, str) and path and "\\" not in path, f"bad path {path!r}")
    parts = Path(path)
    require(not parts.is_absolute() and ".." not in parts.parts and "." not in parts.parts,
            f"path outside repository: {path}")
    full = ROOT / parts
    require(full.resolve().is_relative_to(ROOT.resolve()) and full.is_file() and not full.is_symlink(),
            f"missing or symlinked source: {path}")
    return full


def digest(path):
    return hashlib.sha256(source_file(path).read_bytes()).hexdigest()


def validate_case(folder):
    folder = folder.resolve()
    require(folder.parent == (ROOT / "scenarios").resolve() and re.fullmatch(r"SC-\d\d", folder.name),
            "expected scenarios/SC-XX")
    require((folder / "manifest.json").is_file(), f"missing {folder}/manifest.json")
    m = json.loads((folder / "manifest.json").read_text())
    require(isinstance(m, dict) and m.get("schema_version") == 1, "unknown scenario schema")
    require(m.get("id") == folder.name and isinstance(m.get("title"), str) and m["title"],
            "scenario identity mismatch")
    require(isinstance(m.get("claim_scope"), str) and len(m["claim_scope"]) >= 20,
            "missing explicit narrow claim scope")
    for p in ("scenario.yaml", "claim.lean", "policy.json", "correspondence.md",
              "result.md", "tests/README.md"):
        f = folder / p
        require(f.is_file() and not f.is_symlink(), f"{m['id']}: required file absent: {p}")
    # scenario.yaml uses strict JSON, which is a YAML 1.2 subset. No yaml dependency.
    policy = json.loads((folder / "policy.json").read_text())
    require(policy.get("kind") == "POLICY_REFERENCE_NOT_ENFORCEMENT" and
            policy.get("scenario_id") == m["id"], "policy reference improperly framed")
    spec = json.loads((folder / "scenario.yaml").read_text())
    required = ("id", "title", "sources", "threat_origin", "attacker_controlled",
                "protected_assets", "harmful_transition_or_event", "runtime_boundary",
                "permitted_actions", "forbidden_actions", "complete_receiver_observations",
                "secret_side_information", "horizon_and_persistent_state",
                "honest_task_distribution", "theorem_name", "theorem_assumptions",
                "trusted_computing_base", "checkers", "implementation_hashes",
                "negative_tests", "usefulness_metrics", "environment_evidence",
                "unresolved", "status", "reviewer_decisions")
    require(isinstance(spec, dict) and all(k in spec for k in required),
            f"{m['id']}: incomplete scenario spec")
    require(spec["id"] == m["id"] and spec["title"] == m["title"] and
            spec["status"] == m["declared_status"], "spec/manifest identity or status mismatch")
    axes = m.get("axes")
    require(isinstance(axes, dict) and set(axes) == set(AXES),
            f"{m['id']}: all six applicability axes required")
    for key in AXES:
        a = axes[key]
        require(isinstance(a, dict) and a.get("status") in STATES and
                isinstance(a.get("note"), str) and a["note"].strip() and
                isinstance(a.get("evidence_ids"), list), f"{m['id']}: invalid axis {key}")
        require(a["status"] != "SUPPORTED" or a["evidence_ids"],
                f"{m['id']}: supported axis requires linked evidence")
        require(a["status"] != "NOT_APPLICABLE" or "because" in a["note"].lower(),
                f"{m['id']}: N/A must say because")
    premises = m.get("premises")
    require(isinstance(premises, list) and premises and
            len({p.get("id") for p in premises if isinstance(p, dict)}) == len(premises),
            f"{m['id']}: missing or duplicate premises")
    for p in premises:
        require(isinstance(p, dict) and p.get("axis") in AXES and p.get("status") in STATES
                and isinstance(p.get("text"), str) and p["text"].strip(),
                f"{m['id']}: incomplete named premise")
    ev = m.get("evidence")
    require(isinstance(ev, list) and ev and len({e.get("id") for e in ev}) == len(ev),
            f"{m['id']}: missing or duplicate evidence")
    ids = set()
    for e in ev:
        require(isinstance(e, dict) and isinstance(e.get("id"), str), "invalid evidence")
        ids.add(e["id"])
        require(isinstance(e.get("sha256"), str) and SHA.fullmatch(e["sha256"]),
                f"{e['id']}: unpinned evidence")
        require(digest(e["path"]) == e["sha256"], f"{e['id']}: evidence SHA256 MISMATCH")
        require(e.get("kind") in ("SOURCE", "RECEIPT", "ATTESTATION", "TEST_FIXTURE"),
                f"{e['id']}: missing provenance kind")
    for axis in axes.values():
        require(all(e in ids for e in axis["evidence_ids"]), "axis cites missing evidence ID")
    proofs = m.get("proofs")
    require(isinstance(proofs, list) and proofs, f"{m['id']}: no named model claims")
    for p in proofs:
        require(isinstance(p, dict) and p.get("adversary_class") in CLASSES and
                isinstance(p.get("theorem"), str) and p["theorem"] and
                isinstance(p.get("sha256"), str) and SHA.fullmatch(p["sha256"]),
                f"{m['id']}: incomplete theorem record")
        require(digest(p["file"]) == p["sha256"], f"{m['id']}: theorem SOURCE HASH MISMATCH")
        require(p.get("status_recorded") in ("PROVED_RECORDED", "VERIFIED_RECORDED",
                                             "NOT_CHECKED", "DRAFT"), "bad proof provenance")
    require(isinstance(m.get("negative_tests"), list) and m["negative_tests"], "no falsification tests")
    require(all(isinstance(p, str) and source_file(p) for p in m["negative_tests"]),
            "missing falsification test reference")
    # Explicitly prevent the artifact from announcing deployment assured itself.
    require(m.get("declared_status") in ("CONDITIONAL", "REFUTED_IN_TESTED_HARNESS"),
            "only conditional/refuted scenario records accepted")
    return m


def replay_proofs(folder, m):
    # Intentionally no scenario execution, no automation, and no mutable --update-hashes.
    claim = folder / "claim.lean"
    src = claim.read_text()
    require("import ControlStack." in src and "#print axioms" in src,
            "claim.lean must import a model and request axiom reports")
    # The generated claim has explicit #print axioms for every manifest theorem.
    for p in m["proofs"]:
        require(f"#print axioms {p['theorem']}" in src,
                f"missing axiom command for {p['theorem']}")
    cmd = ["lake", "env", "lean", str(claim.relative_to(ROOT))]
    res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=3600)
    require(res.returncode == 0 and "error:" not in res.stdout,
            f"Lean failure: {res.stdout[-1200:]} {res.stderr[-1200:]}")
    for p in m["proofs"]:
        th = p["theorem"]
        matches = re.findall(
            r"'" + re.escape(th) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
            res.stdout)
        require(len(matches) == 1, f"{th}: no unique axiom report")
        used = {x.strip() for x in matches[0].split(",") if x.strip()}
        require(used <= STANDARD_AXIOMS, f"{th}: unexpected axioms: {used - STANDARD_AXIOMS}")
    return len(m["proofs"])


def report(folder, m, replayed, require_assured):
    states = {k: v["status"] for k, v in m["axes"].items()}
    refuted = any(s == "REFUTED" for s in states.values()) or any(
        p["status"] == "REFUTED" for p in m["premises"])
    blockers = [k for k, s in states.items() if s != "SUPPORTED"]
    blockers.extend(p["id"] for p in m["premises"] if p["status"] != "SUPPORTED")
    verdict = "REFUTED_IN_TESTED_HARNESS" if refuted else "CONDITIONAL"
    # Future promotion requires a separate independently attested process.
    print(f"{m['id']}: {m['title']}")
    print(f"  proofs: {len(m['proofs'])} source digests match; "
          f"{'LEAN_AXIOMS_REPLAYED' if replayed else 'NOT_REPLAYED_THIS_RUN'}")
    print(f"  evidence: {len(m['evidence'])} pinned SHA256 digests match (not environment certification)")
    print(f"  applicability: " + ", ".join(f"{k}={v}" for k, v in states.items()))
    print(f"  blockers: {', '.join(dict.fromkeys(blockers)) or 'none'}")
    print(f"  verdict: {verdict}; DEPLOYMENT_ASSURED never inferred")
    if require_assured:
        raise InvalidCase("no self-promotion to assurance: independent review and "
                          "deployment attestation required")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("folders", nargs="*", default=[])
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--verify-proofs", action="store_true")
    ap.add_argument("--require-assured", action="store_true")
    args = ap.parse_args()
    folders = ([p for p in (ROOT / "scenarios").glob("SC-*") if (p / "manifest.json").exists()]
               if args.all else [ROOT / p for p in args.folders])
    if not folders:
        ap.error("supply scenarios/SC-XX or --all")
    try:
        for folder in sorted(folders):
            m = validate_case(folder)
            replayed = replay_proofs(folder, m) if args.verify_proofs else 0
            report(folder, m, replayed, args.require_assured)
        return 0
    except (InvalidCase, OSError, ValueError, KeyError, json.JSONDecodeError,
            subprocess.TimeoutExpired) as ex:
        print("FAIL CLOSED:", ex, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
