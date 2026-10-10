# One two-agent local-file assurance case

These are **synthetic normalized Compose fixtures**, with invented digest-pinned
image references and runtime inventories. They are not runnable image definitions
or attested running containers. The native broker/receiver boundary is exercised
separately by `tools/run_deployment_boundary.py` (see `SLICE-STATUS.md`).

Run the complete scan/verify/report matrix, including per-fixture Lean instances:

```sh
lake build ControlStack.Deployment.Contracts
python3 tools/run_deployment_matrix.py --output /tmp/slice-matrix --lean
python3 tools/cstack.py check --fast --only deployment
```

For the single clean candidate:

```sh
python3 tools/cstack.py scan examples/compose-two-agent/clean.compose.json \
  --runtime examples/compose-two-agent/clean.runtime.json \
  --sha256 "$(python3 -c 'import json; print(json.load(open("examples/compose-two-agent/expected.json"))["clean"]["compose_sha256"])')" \
  --output /tmp/clean-ir.json
python3 tools/cstack.py verify /tmp/clean-ir.json --lean --output /tmp/clean-bundle.json
python3 tools/cstack.py report /tmp/clean-bundle.json --output /tmp/clean-report.md
```

Exit codes: scan/report 0 on valid output; verify 0 for CONDITIONAL, 1 for
UNASSURED; all commands 2 on invalid input/pin, unavailable kernel checking or
usage errors. Without `--lean`, kernel obligations remain UNASSESSED and the
report explicitly describes a conditional configuration candidate. No ASSURED
result is implemented. `--lean` checks raw node/edge facts and instantiates the
existing protocol contracts; it never upgrades residual runtime faithfulness.

The mutations are writable sink mount, agent broker-DB access, trusted-role UID
collision, privileged container, host network, alternate deputy sink credentials,
and one UNKNOWN unsupported device feature. Each must be UNASSURED and name its
reason even if authorization says FORBIDDEN. Negative controls with disabled
payload, nonce/budget and receiver checks exist in the reused Lean libraries.
