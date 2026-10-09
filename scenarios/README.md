# Scenario bundles

The bundles implement SCENARIO-CATALOG.md section 6 as references to existing Lean and runtime artifacts, not copies. Historical receipts remain in their existing locations. No scenario/VM experiments are run or changed by this work.

Static structural, proof-record and SHA checks (no Lean invocation):

    python3 tools/check_scenarios.py

For machine output use --json. Use --require-clear for strict exit codes: 2 for unresolved prerequisites, 3 for recorded refutation/failed evidence or usefulness. Neither mode independently kernel-checks Lean or authorizes a deployment claim. Each assumption must have separate proof, evidence and applicability axes. Failure and success from distinct environments must never be pooled. SC-01's later VM usefulness replay fails with 0/64 lifetimes in both conditions at the frozen 0.25-second deadline.

Historical assurance files, runtime evidence receipts and old Lean module names remain at their original paths. Six reviewed proof implementations were relocated byte-for-byte into Core/Families/Witnesses, and compatibility facades preserve their old imports.

## Merge canonical paths

[Theorem registry](../THEOREM-REGISTRY.md) (source inventory, not a proof run); [scenario index](INDEX.md); [ROADMAP](../ROADMAP.md) (one authoritative status entry point). SC-27 is draft until independently rooted provenance/attestation exists; its `claim.lean` imports a narrower audit-dispatch theorem only. No preregistrations or receipts were regenerated.


## Hardening follow-up (candidate branch only)

Each `manifest.json` additionally requires a **usefulness** status per named premise and a complete `scope_axes` object: threat coverage, runtime correspondence, environment boundary, lifetime/composition, usefulness and independent review. These record **obligations**, not positive assurance. Missing fields fail closed; `SUPPORTED` is deliberately not accepted as a self-reported scope state. A checker pass only establishes syntactic consistency, local source/digest matching, and index linkage. For future experiment drafts use [prereg/](../prereg/) rather than creating additional scenario-local prereg folders.
