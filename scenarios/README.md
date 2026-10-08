# Scenario bundles

The bundles implement SCENARIO-CATALOG.md section 6 as references to existing Lean and runtime artifacts, not copies. Historical receipts remain in their existing locations. No scenario/VM experiments are run or changed by this work.

Static structural, proof-record and SHA checks (no Lean invocation):

    python3 tools/check_scenarios.py

For machine output use --json; for nonzero exit on unresolved/refuted applicability, failed receipts or unbound evidence use --require-clear. Neither mode independently kernel-checks Lean or authorizes a deployment claim. Each assumption must have separate proof, evidence and applicability axes. Failure and success from distinct environments must never be pooled. SC-01's later VM usefulness replay fails with 0/64 lifetimes in both conditions at the frozen 0.25-second deadline.

Existing source code, historical assurance files and module names are not moved, preserving CI and imports.

## Merge canonical paths

[Theorem registry](../THEOREM-REGISTRY.md) (source inventory, not a proof run); [scenario index](INDEX.md); [ROADMAP](../ROADMAP.md) (one authoritative status entry point). SC-27 is draft until independently rooted provenance/attestation exists; its `claim.lean` imports a narrower audit-dispatch theorem only. No preregistrations or receipts were regenerated.
