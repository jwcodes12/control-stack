#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 gateway/test_lifetime.py
python3 gateway/scenario/test_scenario.py
python3 gateway/test_gateway.py
axioms=$(mktemp)
trap 'rm -f "$axioms"' EXIT
lake env lean ControlStack/ScenarioARepair.lean > "$axioms"
cat "$axioms"
python3 - "$axioms" <<'PY'
import re,sys
report=open(sys.argv[1]).read()
for name in ['transcript_card','repair_recovery','repair_target']:
    entries=re.findall(r"'ControlStack.ScenarioARepair\."+name+r"' depends on axioms: \[([^\]]*)\]",report)
    assert len(entries)==1,name
    assert set(x.strip() for x in entries[0].split(',')) <= {'propext','Classical.choice','Quot.sound'},name
print('ScenarioARepair: three theorem axiom checks passed')
PY
if [[ ${1:-} == --run && $# == 2 ]]; then
    python3 gateway/scenario/run.py --output "$2"
    python3 gateway/scenario/check_receipt.py "$2"
elif [[ ${1:-} == --receipt && $# == 2 ]]; then
    python3 gateway/scenario/check_receipt.py "$2"
elif [[ $# != 0 ]]; then
    echo 'usage: gateway/scenario/check.sh [--run OUTPUT | --receipt RECEIPT]' >&2
    exit 1
fi
