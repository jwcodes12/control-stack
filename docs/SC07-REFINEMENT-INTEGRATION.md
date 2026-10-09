# SC-07 refinement integration review (2026-10-09)

This branch integrates the existing 411-line `ControlStack.SC07Refinement` module into SC-07's manifest, claim, and portfolio TrustRoot graph.

## Formal link and scope

- `SC07Refinement.simulation_run` gives a forward simulation from an idealized nftables gateway event machine to `SC07Liveness`.
- `concrete_safe` transfers quota and allowlist safety; `concrete_wire_lt` proves strictly less than the threshold per window with the quota rule enabled and Q > 0; `concrete_halt_freezes` transfers HALT log stability; `sink_within_quota` assumes sink delivery is no greater than the forwarded payload.
- The theorem statements describe *the modeled packet machine*, not arbitrary Linux kernels, gateway configurations, bypass routes, timing channels, raw secret information flow, or TCP retransmission behavior.
- The Python/nftables-to-concrete-machine correspondence is **not proved**. A single-host preregistered benign run provides TESTED_NOT_PROVED evidence, not deployment assurance.
- `model_runtime_correspondence` is explicitly recorded as an unresolved applicability premise. TrustRoot's refinement edge therefore does not erase the residual `implementation_conformance` root.

## Integrity and review

- Source hash (SHA-256) of `ControlStack/Scenarios/SC07Refinement.lean`: `7c3f3b0e0e70abaf4bdfd514014f86624495b6aa6b59b1ab1052dc010c85eca0`.
- Original SC-07 evidence and preregistration were not modified or rerun.
- All new manifest theorems are named in `scenarios/SC-07/claim.lean` with `#check` and `#print axioms`.
- No assertion of independent human signoff is made.

## Verification required on the PR

```sh
lake exe cache get && lake build
python3 tools/cstack.py check --fast
python3 tools/cstack.py check --full
python3 tools/cstack.py evidence SC-07
```

Do not merge unless the CI checks are green; inspect generated-data drift and theorem statement fidelity separately.

The generated theorem registry was also refreshed to pin the changed `TrustRoot.lean` blob, without elevating source-only declarations to verified status.
