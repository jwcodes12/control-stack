#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lean ControlStack/EgressGate.lean > "$report"
cat "$report"
python3 - "$report" <<'PY'
import re,sys
log=open(sys.argv[1]).read()
allowed={'propext','Quot.sound','Classical.choice'}
for name in ['lookup_pinned','direct_no_effect','step_safe','trace_safe','failed_launch','crash_closed']:
    match=re.findall(r"'ControlStack.EgressGate\."+name+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    assert len(match)==1,(name,'missing or duplicate axiom report')
    assert {a.strip() for a in match[0].split(',') if a.strip()}<=allowed,name
assert not re.search(r'\b(sorry|admit)\b',open('ControlStack/EgressGate.lean').read())
print('EgressGate: six theorem axiom checks passed')
PY
