#!/usr/bin/env python3
"""Batch fixture verdicts and all per-fixture Lean certificates/axiom checks.

Every raw IR still receives its own positive/negative Accepted certificate,
SC26 safety and once-only instantiations, and nine standard-axiom reports.
This eliminates repeated lake builds and Lean process startup, NOT proof gates.
"""
if not __debug__:
    raise SystemExit("Refusing to run a certificate checker under python -O")
import json
import re
from collections import Counter
import subprocess
import tempfile
from pathlib import Path

from tools.check_deployment_lean import ROOT, projection

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
CONTRACTS = (
    "ControlStack.Deployment.protocol_safe",
    "ControlStack.Deployment.one_use",
    "ControlStack.Deployment.gate_contract",
    "ControlStack.Deployment.broker_contract",
    "ControlStack.Deployment.runtime_exclusive",
    "ControlStack.Deployment.deployment_safe",
)
HEADER = (
    "import ControlStack.Deployment.Contracts\n"
    "open ControlStack.Deployment\n"
    "set_option maxRecDepth 10000\n"
    "set_option maxHeartbeats 40000000\n"
    "namespace SliceBatch\n"
)


def lean(path):
    run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                         capture_output=True, text=True)
    if run.returncode:
        raise ValueError(run.stdout + run.stderr)
    return run.stdout + run.stderr


def required_axiom_report_names(n_items):
    """Every fixture has three uniquely named reports plus six shared contracts."""
    return Counter(
        [name for _ in range(n_items) for name in CONTRACTS]
        + [f"SliceBatch.{kind}_{i}" for i in range(n_items)
           for kind in ("facts", "contract_checked", "one_use_checked")]
    )


def check_axiom_reports(output, n_items):
    """Reject missing, duplicated, substituted, or nonstandard axiom reports.

    Counting reports alone is insufficient: a duplicated report could hide a
    missing or malformed per-fixture certificate.
    """
    reports = re.findall(
        r"'([^']+)' (does not depend on any axioms|depends on axioms: \\[([^\\]]*)\\])",
        output,
    )
    found = Counter(name for name, _, _ in reports)
    required = required_axiom_report_names(n_items)
    if found != required:
        raise ValueError(
            f"Missing, unexpected, or duplicated per-certificate axiom reports: "
            f"required={required}, found={found}\\n{output}"
        )
    for name, _, axioms in reports:
        disallowed = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
        if disallowed:
            raise ValueError(f"Disallowed axioms for {name}: {sorted(disallowed)}\\n{output}")
    if "sorryAx" in output:
        raise ValueError("Unsafe sorryAx in batch Lean report:\\n" + output)


def check_many_fixtures(items):
    if not items:
        raise ValueError("No raw IR fixtures supplied")
    subprocess.run(["lake", "build", "ControlStack.Deployment.Contracts"],
                   cwd=ROOT, check=True, capture_output=True, text=True)
    definitions = [
        f"def instance_{i} : IR := {projection(ir)}\n"
        for i, (_, ir) in enumerate(items)
    ]
    instances = ",".join(f"instance_{i}" for i in range(len(items)))
    evaluation = (
        '#eval IO.println ("BATCH_ACCEPTED:" ++ String.intercalate "," '
        f'(([{instances}] : List IR).map (fun d => toString (decide (Accepted d)))))\n'
    )
    with tempfile.TemporaryDirectory(prefix="cstack-fixtures-", dir=ROOT / ".git") as tmp:
        file = Path(tmp) / "Certificates.lean"
        file.write_text(HEADER + "".join(definitions) + evaluation + "end SliceBatch\n")
        output = lean(file)
        verdict = next((line for line in output.splitlines()
                        if line.startswith("BATCH_ACCEPTED:")), None)
        if verdict is None:
            raise ValueError("Lean did not return batch verdicts:\n" + output)
        values = verdict.removeprefix("BATCH_ACCEPTED:").split(",")
        if len(values) != len(items) or any(v not in {"true", "false"} for v in values):
            raise ValueError("Malformed Lean verdicts: " + verdict)
        accepted = [x == "true" for x in values]
        obligations = []
        reports = []
        for i, (_, ir) in enumerate(items):
            # projection(ir) above validates the raw IR, as in the single-file checker.
            services = [n["facts"] for n in ir["nodes"] if n["type"] == "service"]
            receiver = next((f["uid"] for f in services if f["role"] == "receiver"), 0)
            approvers = [f["uid"] or 0 for f in services if f["role"] == "approver"]
            admins = [f["uid"] or 0 for f in services if f["role"] == "broker"]
            cap = ir["snapshot"]["budget"]
            outcome = "Accepted" if accepted[i] else "¬ Accepted"
            obligations.append(
                f"theorem facts_{i} : {outcome} instance_{i} := by decide\n"
                f"def principals_{i} : ControlStack.SC26.Roles := "
                f"roles instance_{i} {receiver or 0} {approvers} {admins}\n"
                f"theorem contract_checked_{i} (ops : List ControlStack.SC26.Op) "
                f"(hops : ∀ o ∈ ops, ControlStack.SC26.legal principals_{i} o) : "
                f"ControlStack.SC26.Good principals_{i} {cap} "
                f"(ControlStack.SC26.run principals_{i} {cap} "
                f"ControlStack.SC26.full ControlStack.SC26.init ops) := "
                f"protocol_safe principals_{i} {cap} ops hops\n"
                f"theorem one_use_checked_{i} (ops : List ControlStack.SC26.Op) : "
                f"(ControlStack.SC26.run principals_{i} {cap} "
                f"ControlStack.SC26.full ControlStack.SC26.init ops).reserved.Nodup := "
                f"one_use principals_{i} {cap} ops\n"
            )
            reports.extend(f"#print axioms {claim}\n" for claim in CONTRACTS)
            reports.extend(
                f"#print axioms SliceBatch.{kind}_{i}\n"
                for kind in ("facts", "contract_checked", "one_use_checked")
            )
        file.write_text(
            HEADER + "".join(definitions) + "".join(obligations)
            + "end SliceBatch\n" + "".join(reports)
        )
        axioms = lean(file)
        check_axiom_reports(axioms, len(items))
        return accepted


def main():
    paths = sorted((ROOT / "security_ir" / "fixtures").glob("*.json"))
    if not paths:
        raise SystemExit("No raw IR fixtures found")
    expected = json.loads((ROOT / "examples/compose-two-agent/expected.json").read_text())
    items = [(p.stem, json.loads(p.read_text())) for p in paths]
    results = check_many_fixtures(items)
    for (name, _), accepted in zip(items, results, strict=True):
        if accepted != expected[name]["lean_accepted"]:
            raise SystemExit(f"FAIL: {name}: Lean says {accepted}")
        print(f"PASS: {name} accepted={accepted} (9 axiom checks)")
    print(f"PASS: {len(items)} kernel-checked fixtures with full per-fixture obligations")


if __name__ == "__main__":
    main()
