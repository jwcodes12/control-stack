#!/usr/bin/env bash
# Copy the two covert-channel modules into the narrow project, rename the namespace path, build, and check that every
# public theorem depends only on the standard axioms.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p CovertCI
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/CovertChannel.lean > CovertCI/CovertChannel.lean
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/GatewayModel.lean > CovertCI/GatewayModel.lean
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/CovertNoGo.lean > CovertCI/CovertNoGo.lean
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/ScenarioARepair.lean > CovertCI/ScenarioARepair.lean
cp ../../ControlStack/AuditGate.lean CovertCI/AuditGate.lean
cp ../../ControlStack/AuditDispatch.lean CovertCI/AuditDispatch.lean
printf 'import CovertCI.CovertChannel\nimport CovertCI.GatewayModel\nimport CovertCI.CovertNoGo\nimport CovertCI.ScenarioARepair\nimport CovertCI.AuditGate\nimport CovertCI.AuditDispatch\n' > CovertCI.lean
lake exe cache get
lake build 2>&1 | tee build.log
python3 - <<'PY'
import re, sys, json
# R2-7: every listed theorem must have exactly one axiom report, and its axioms must be a subset of the allowlist.
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
THMS = ["covert_bound", "covert_bound_schema", "covert_bound_lifetime", "attain_embedding", "design_point",
        "gateway_bound", "gateway_bound_reachable", "other_blanks", "controllable_leak", "one_bit_coordinates", "invariant_preserved", "trace_safe", "app_cannot_effect", "dispatch_audit_first",
        "transcript_card", "repair_recovery", "repair_target"]
log = open("build.log").read().replace("\n", " ")
report, bad = {}, []
for t in THMS:
    m = re.findall(r"'[A-Za-z0-9_.]*\." + t + r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(m) != 1:
        bad.append(f"{t}: expected exactly one axiom report, found {len(m)}"); continue
    axs = {a.strip() for a in m[0][1].split(",") if a.strip()}
    report[t] = sorted(axs)
    if not axs <= ALLOWED:
        bad.append(f"{t}: non-allowlisted axioms {sorted(axs - ALLOWED)}")
json.dump(report, open("axiom_report.json", "w"), indent=1)
print(json.dumps(report, indent=1))
if bad:
    print("\n".join(bad)); sys.exit(1)
print("all theorems use only allowlisted axioms")
PY
