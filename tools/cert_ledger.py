#!/usr/bin/env python3
"""Typed assumption ledger of a Lean certificate (ControlStack/Core/Cert.lean), checked against scenario manifests.

The ledger comes from Lean itself. The tool writes a small file that imports ControlStack.Core.Cert and
`#eval`s `ControlStack.Cert.ledgerJson <ledger>`, runs `lake env lean` on it, and parses the JSON. The default
ledger is `ControlStack.Cert.stackLedger`; Lean proves it equal to the stack certificate's actual premise list
(`stack_ledger_eq`). `--json-file` reads a canned JSON ledger instead, for tests.

Outputs and checks:
(a) the ledger grouped by premise kind: proof_obligation, correspondence, measurement, environment,
    organisational;
(b) `--check-manifest scenarios/SC-XX/manifest.json`, fail-closed:
    - every premise of a NON-proof kind that concerns the scenario must map, through MAPPING below, to
      assumption ids that ALL appear in the manifest's `assumptions`;
    - a premise concerns scenario SC-XX when its id (the text before ':') starts with "SCXX.";
    - an unmapped premise, an unknown kind, a missing id or an unreadable manifest is a failure;
    - every proof_obligation premise must name a theorem whose local name occurs exactly once in
      THEOREM-REGISTRY.json.

Exit codes: 0 = ledger printed / checks pass; 1 = check failed or error.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KINDS = ("proof_obligation", "correspondence", "measurement", "environment", "organisational")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")

# premise id -> manifest assumption ids that must cover it, per scenario
MAPPING = {
    "SC-26": {
        "SC26.legal": ["credential_separation"],
        "SC26.legal_realized": ["credential_separation"],
        "SC26.sound_config": ["model_runtime_correspondence", "receiver_idempotency"],
    },
}


class LedgerError(Exception):
    pass


def premise_id(name):
    return name.split(":", 1)[0].strip()


def validate(entries):
    if not isinstance(entries, list) or not entries:
        raise LedgerError("ledger must be a nonempty JSON list")
    for e in entries:
        if not isinstance(e, dict) or not isinstance(e.get("name"), str) or not e["name"].strip():
            raise LedgerError(f"invalid ledger entry: {e!r}")
        if e.get("kind") not in KINDS:
            raise LedgerError(f"unknown premise kind {e.get('kind')!r} for {e['name']!r}")
        if e["kind"] == "proof_obligation" and not (isinstance(e.get("theorem"), str) and e["theorem"]):
            raise LedgerError(f"proof obligation without theorem: {e['name']!r}")
    return entries


def lean_ledger(ledger="ControlStack.Cert.stackLedger", root=ROOT, timeout=1800):
    """Run Lean to render a typed ledger as JSON."""
    if not IDENT.match(ledger):
        raise LedgerError(f"not a Lean identifier: {ledger!r}")
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "LedgerOut.lean"
        src.write_text("import ControlStack.Core.Cert\n"
                       f"#eval IO.println (ControlStack.Cert.ledgerJson {ledger})\n")
        try:
            proc = subprocess.run(["lake", "env", "lean", str(src)], cwd=root, capture_output=True, text=True,
                                  timeout=timeout)
        except (OSError, subprocess.TimeoutExpired) as e:
            raise LedgerError(f"lean failed to run: {e}") from e
    if proc.returncode != 0 or "error" in proc.stdout.lower().split("[", 1)[0]:
        raise LedgerError(f"lean exited {proc.returncode}: {(proc.stdout + proc.stderr).strip()[:2000]}")
    lines = [ln for ln in proc.stdout.splitlines() if ln.startswith("[")]
    if len(lines) != 1:
        raise LedgerError(f"expected one JSON line from lean, got {len(lines)}: {proc.stdout[:2000]}")
    try:
        return validate(json.loads(lines[0]))
    except json.JSONDecodeError as e:
        raise LedgerError(f"lean printed invalid JSON: {e}") from e


def grouped(entries):
    """kind -> deduplicated names, in ledger order"""
    out = {k: [] for k in KINDS}
    for e in entries:
        label = e["name"] + (f"  [discharged by {e['theorem']}]" if e["kind"] == "proof_obligation" else "")
        if label not in out[e["kind"]]:
            out[e["kind"]].append(label)
    return out


def check_manifest(entries, manifest_path, registry_path=ROOT / "THEOREM-REGISTRY.json", mapping=MAPPING):
    """Return a list of failure strings (empty = pass)."""
    failures = []
    try:
        manifest = json.loads(Path(manifest_path).read_text())
        sid = manifest["id"]
        ids = {a["id"] for a in manifest["assumptions"]}
    except (OSError, ValueError, KeyError, TypeError) as e:
        return [f"manifest unreadable or malformed: {e}"]
    if not re.fullmatch(r"SC-\d\d", str(sid)):
        return [f"manifest id not a scenario id: {sid!r}"]
    prefix = sid.replace("-", "") + "."
    table = mapping.get(sid, {})
    try:
        registry = json.loads(Path(registry_path).read_text())
        keys = [r["key"] for r in registry if isinstance(r, dict) and isinstance(r.get("key"), str)]
    except (OSError, ValueError) as e:
        return [f"registry unreadable: {e}"]
    seen = set()
    for e in entries:
        pid = premise_id(e["name"])
        if e["kind"] == "proof_obligation":
            local = e["theorem"].rsplit(".", 1)[-1]
            hits = [k for k in keys if k.endswith("::" + local)]
            if len(hits) != 1:
                failures.append(f"proof obligation {pid!r}: theorem {e['theorem']!r} found {len(hits)} times in "
                                "the registry (need exactly 1)")
            continue
        if not pid.startswith(prefix) or (pid, e["kind"]) in seen:
            continue
        seen.add((pid, e["kind"]))
        if pid not in table:
            failures.append(f"{e['kind']} premise {pid!r} concerns {sid} but has no manifest mapping")
            continue
        for aid in table[pid]:
            if aid not in ids:
                failures.append(f"{e['kind']} premise {pid!r} needs manifest assumption {aid!r}, absent from {sid}")
    if not seen:
        failures.append(f"no premise of the certificate concerns {sid}: nothing to check (fail closed)")
    return failures


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ledger", default="ControlStack.Cert.stackLedger",
                    help="Lean term of type List (String × PremiseKind)")
    ap.add_argument("--json-file", type=Path, help="read a JSON ledger instead of running Lean")
    ap.add_argument("--check-manifest", type=Path, help="scenario manifest to check the ledger against")
    ap.add_argument("--registry", type=Path, default=ROOT / "THEOREM-REGISTRY.json")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args(argv)
    try:
        entries = validate(json.loads(args.json_file.read_text())) if args.json_file else lean_ledger(args.ledger)
    except (LedgerError, OSError, ValueError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    groups = grouped(entries)
    failures = check_manifest(entries, args.check_manifest, args.registry) if args.check_manifest else []
    if args.json:
        print(json.dumps({"grouped": groups, "failures": failures}, indent=2, ensure_ascii=False))
    else:
        for k in KINDS:
            print(f"{k} ({len(groups[k])})")
            for n in groups[k]:
                print(f"  - {n}")
        if args.check_manifest:
            print(f"\nmanifest check: {args.check_manifest}")
            print("  PASS" if not failures else "\n".join(f"  FAIL: {f}" for f in failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
