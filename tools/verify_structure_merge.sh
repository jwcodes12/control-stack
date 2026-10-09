#!/usr/bin/env bash
# Read-only acceptance replay. No evidence, preregistration, or hashes are rewritten.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null || { echo 'Lean Lake is required' >&2; exit 2; }
command -v python3 >/dev/null || { echo 'Python 3 is required' >&2; exit 2; }

lake exe cache get
lake build ControlStack
python3 tools/build_registry.py --check
python3 tools/build_status.py --check
python3 tools/check_scenarios.py
python3 -m unittest tools.test_check_scenarios
python3 tools/test_ctrlcert.py

# Scenario claims are loose Lean files, not root-module build targets.
# Capture and reject every nonstandard reported axiom.
tmp_claims="$(mktemp)"
tmp_sc01="$(mktemp)"
trap 'rm -f "$tmp_claims" "$tmp_sc01"' EXIT
for claim in scenarios/SC-{01..28}/claim.lean; do
  echo "Compiling $claim"
  lake env lean "$claim" >>"$tmp_claims" 2>&1 || {
    cat "$tmp_claims" >&2
    exit 1
  }
done
python3 - "$tmp_claims" <<'PY'
import re
import sys
from pathlib import Path
output = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reports = re.findall(r"'[^']+' depends on axioms: \[([^\]]*)\]", output)
for report in reports:
    used = {s.strip() for s in report.split(',') if s.strip()}
    if used - allowed:
        raise SystemExit(f'NONSTANDARD AXIOMS: {sorted(used - allowed)}')
if 'error:' in output or 'sorryAx' in output:
    raise SystemExit('Lean output has an error or sorry axiom')
print(f'Scenario claim axiom reports inspected: {len(reports)}')
PY

# A new machine may fail only on the frozen old-host OpenSSL binding in step 5.
set +e
python3 tools/check_sc01_case.py >"$tmp_sc01" 2>&1
sc01_rc=$?
set -e
if [[ "$sc01_rc" == 3 ]]; then
  grep -q '^VERDICT: HYPOTHESIS_REFUTED' "$tmp_sc01" || {
    cat "$tmp_sc01" >&2; exit 1;
  }
elif [[ "$sc01_rc" == 1 ]]; then
  for marker in '1. Lean (case chain)' '2. hashes' '3. gateway differential test' '4. usefulness receipt' '5. side-certificate hypothesis vs measured evidence'; do
    grep -Fq "$marker" "$tmp_sc01" || { cat "$tmp_sc01" >&2; exit 1; }
  done
  grep -Fq 'shared file changed' "$tmp_sc01" || { cat "$tmp_sc01" >&2; exit 1; }
  grep -Fq 'cache receipt verifier failed' "$tmp_sc01" || { cat "$tmp_sc01" >&2; exit 1; }
  echo 'SC-01: steps 1-4 reached; step 5 failed only at host-bound cache receipt check'
else
  cat "$tmp_sc01" >&2
  echo "Unexpected SC-01 return code: $sc01_rc" >&2
  exit 1
fi
printf '\nAcceptance commands finished. This does not independently attest runtime scope.\n'
