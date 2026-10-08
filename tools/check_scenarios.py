#!/usr/bin/env python3
"""Validate scenario bundles and report proof/evidence/applicability separately.
Static only: no Lean, runtime, VM, network, or subprocess execution.
Recorded kernel results are NOT rechecked and cannot imply deployment assurance.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
AXES = {
    "proof": {"THEOREM_VERIFIED", "NOT_PROVED", "NOT_APPLICABLE"},
    "evidence": {"RUNTIME_VALIDATED", "TESTED_NOT_PROVED", "OBSERVED_FAILURE", "NOT_RUN", "NOT_APPLICABLE"},
    "applicability": {"ESTABLISHED", "UNRESOLVED", "REFUTED"},
}
DOCS = ("threat.md", "claim.lean", "policy.json", "correspondence.md", "result.md", "tests/README.md")
SHA = re.compile(r"[a-f0-9]{64}$")


class Invalid(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise Invalid(reason)


def file_at(root, name):
    need(isinstance(name, str) and bool(name), "empty/invalid file path")
    p = PurePosixPath(name)
    need(not p.is_absolute() and ".." not in p.parts and "." not in p.parts,
         f"unsafe path: {name}")
    f = (root / p).resolve()
    need(root.resolve() in f.parents and f.is_file(), f"missing or escaping file: {name}")
    return f


def artifact(root, a, kind):
    need(isinstance(a, dict), f"{kind}: expected object")
    f = file_at(root, a.get("path"))
    digest = a.get("sha256")
    if digest is None:
        need(kind == "evidence" and a.get("binding") == "UNBOUND",
             f"{kind}: missing SHA-256 requires explicit UNBOUND evidence")
        return False
    need(isinstance(digest, str) and SHA.fullmatch(digest),
         f"{kind}: invalid SHA-256")
    need(hashlib.sha256(f.read_bytes()).hexdigest() == digest,
         f"{kind}: hash mismatch at {a['path']}")
    return True


def verify(root, sid):
    root = root.resolve()
    need(bool(re.fullmatch(r"SC-\d\d", sid)), f"bad scenario id: {sid}")
    for p in DOCS:
        file_at(root, f"scenarios/{sid}/{p}")
    m = json.loads(file_at(root, f"scenarios/{sid}/manifest.json").read_text())
    need(isinstance(m, dict) and m.get("schema_version") == 1 and m.get("id") == sid,
         f"{sid}: invalid schema/id")
    for field in ("title", "bad_event", "adversary", "refutation", "scope"):
        need(isinstance(m.get(field), str) and bool(m[field].strip()),
             f"{sid}: missing {field}")
    fs = m.get("families")
    need(isinstance(fs, list) and bool(fs) and len(fs) == len(set(fs)) and
         all(f in [f"F{i}" for i in range(1, 9)] for f in fs),
         f"{sid}: invalid proof families")
    need(m.get("status") in {"DRAFT", "CONDITIONAL", "FAILED"},
         f"{sid}: status must not claim deployment assurance")
    proofs, evs, assumptions = m.get("theorems"), m.get("evidence"), m.get("assumptions")
    need(isinstance(proofs, list) and isinstance(evs, list) and
         isinstance(assumptions, list) and bool(assumptions),
         f"{sid}: proof/evidence arrays and nonempty assumption list required")
    names = set()
    for x in proofs:
        need(isinstance(x, dict) and isinstance(x.get("name"), str) and x["name"] and
             x["name"] not in names, f"{sid}: missing/duplicate theorem")
        names.add(x["name"])
        need(x.get("recorded_status") in {"KERNEL_CHECK_RECORDED", "NOT_CHECKED"},
             f"{sid}: unsupported theorem status")
        artifact(root, x, "proof")
    # Registry is a source-derived lexical inventory, NOT a kernel verification.
    # Manifest names and claim commands cannot be invented or self-promoted.
    if proofs:
        registry_file = root / "THEOREM-REGISTRY.json"
        need(registry_file.is_file(), f"{sid}: missing generated theorem registry")
        records = json.loads(registry_file.read_text())
        need(isinstance(records, list), f"{sid}: invalid theorem registry")
        registered = {item["key"] for item in records
                      if isinstance(item, dict) and isinstance(item.get("key"), str)}
        claim = file_at(root, f"scenarios/{sid}/claim.lean").read_text()
        for x in proofs:
            local = x["name"].rsplit(".", 1)[-1]
            key = f"{x['path']}::{local}"
            need(key in registered, f"{sid}: theorem absent from registry: {key}")
            source = file_at(root, x["path"]).read_text()
            need(re.search(r"(?m)^\s*(?:(?:private|protected)\s+)?"
                           r"(?:theorem|lemma)\s+" + re.escape(local) + r"\b", source) is not None,
                 f"{sid}: theorem not declared in cited source: {key}")
            need(any(re.search(r"(?m)^\s*#" + cmd + r"\s+" +
                               re.escape(x["name"]) + r"\s*$", claim)
                     for cmd in ("check", "print axioms")),
                 f"{sid}: claim.lean does not check named theorem: {x['name']}")

    failed, unbound = [], []
    for x in evs:
        need(isinstance(x, dict) and isinstance(x.get("purpose"), str) and x["purpose"],
             f"{sid}: evidence purpose required")
        need(x.get("outcome") in {"PASS", "FAIL", "NOT_RUN", "UNKNOWN"},
             f"{sid}: invalid evidence outcome")
        if not artifact(root, x, "evidence"):
            unbound.append(x["path"])
        if x["outcome"] == "FAIL":
            failed.append(x["path"])
    blockers = []
    ids = set()
    for a in assumptions:
        need(isinstance(a, dict) and isinstance(a.get("id"), str) and a["id"] and
             a["id"] not in ids and isinstance(a.get("text"), str) and a["text"],
             f"{sid}: invalid/duplicate assumption")
        ids.add(a["id"])
        for axis, choices in AXES.items():
            need(a.get(axis) in choices, f"{sid}/{a['id']}: invalid/missing {axis}")
        if a["applicability"] != "ESTABLISHED":
            blockers.append(f"{a['id']}:{a['applicability']}")
    proof = ("NO_THEOREM_LISTED" if not proofs else "RECORDED_NOT_RECHECKED")
    if proofs and any(x["recorded_status"] != "KERNEL_CHECK_RECORDED" for x in proofs):
        proof = "INCOMPLETE_RECORD"
    evidence = ("FAILURE_RECORDED" if failed else "UNBOUND_EVIDENCE" if unbound
                else "RECORDS_NOT_RERUN" if evs else "NO_EVIDENCE")
    applicability = ("BLOCKED" if blockers or failed or unbound
                     else "NOT_INDEPENDENTLY_REVIEWED")
    return dict(id=sid, status=m["status"], proof=proof, evidence=evidence,
                applicability=applicability, blocking_assumptions=blockers,
                failed_receipts=failed, unbound_evidence=unbound,
                deployment_assured=False)


def main(argv=None, root=ROOT):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("scenarios", nargs="*")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--require-clear", action="store_true")
    args = ap.parse_args(argv)
    folder = root / "scenarios"
    if not folder.is_dir():
        print("FAIL: no scenarios directory", file=sys.stderr)
        return 1
    ids = args.scenarios or sorted(p.name for p in folder.iterdir() if p.is_dir())
    reports, errors = [], []
    for sid in ids:
        try:
            reports.append(verify(root, sid))
        except (Invalid, ValueError, OSError, TypeError) as e:
            errors.append(f"{sid}: {e}")
    if args.json:
        print(json.dumps({"reports": reports, "errors": errors}, indent=2))
    else:
        for r in reports:
            print(f"{r['id']}: proof={r['proof']} evidence={r['evidence']} "
                  f"applicability={r['applicability']} deployment_assured=NO")
            if r["blocking_assumptions"]:
                print("  blockers:", ", ".join(r["blocking_assumptions"]))
            if r["failed_receipts"]:
                print("  failed receipts:", ", ".join(r["failed_receipts"]))
        for e in errors:
            print("FAIL:", e, file=sys.stderr)
    if errors:
        return 1
    return 2 if args.require_clear and any(r["applicability"] !=
                        "NOT_INDEPENDENTLY_REVIEWED" for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
