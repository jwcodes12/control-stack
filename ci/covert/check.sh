#!/usr/bin/env bash
# Copy the two covert-channel modules into the narrow project, rename the namespace path, build, and check that every
# public theorem depends only on the standard axioms.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p CovertCI
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/CovertChannel.lean > CovertCI/CovertChannel.lean
sed 's/^import ControlStack.CovertChannel/import CovertCI.CovertChannel/' ../../ControlStack/GatewayModel.lean > CovertCI/GatewayModel.lean
printf 'import CovertCI.CovertChannel\nimport CovertCI.GatewayModel\n' > CovertCI.lean
lake exe cache get
lake build 2>&1 | tee build.log
for t in covert_bound covert_bound_schema covert_bound_lifetime attain_embedding design_point gateway_bound other_blanks; do
  line=$(grep -A2 "\.$t' depends on axioms" build.log | tr '\n' ' ' || true)
  [ -n "$line" ] || { echo "MISSING axiom report for $t"; exit 1; }
  echo "$line" | grep -q "sorryAx" && { echo "SORRY in $t"; exit 1; }
  echo "ok $t"
done
