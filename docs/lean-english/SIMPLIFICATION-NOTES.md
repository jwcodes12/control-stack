# Consolidated Lean simplification — PR #55 (2026-10-11)

**Scope:** reuse-audit first, then model-only changes on one working branch. This is an engineering review note, **not an independent human review** and **not a deployment-assurance upgrade**. The existing release status is scoped R2 / CONDITIONAL. No malicious inputs, live containers, privileged modes, or frozen evidence were changed.

## What changed

1. `REUSE-AUDIT.md`: all 187 English headline rows mapped to source and registry; 183 distinct qualified names, four repeat rows; conservative candidates distinguished from proven substitutions.
2. `ControlStack/Deployment/Provenance.lean`: integrates the G0 draft's review/approval invariant and its preservation across guarded `TrustedBroker.Step` and traces. The theorem for published nonces requires the abstract `BrokerProtocolRefinement` premise. These *final-state* role/lease/record facts are not a historical signed per-file release receipt.
3. `ControlStack/Deployment/ProvenanceWitnesses.lean`: one guarded, positive abstract trace and an unreviewed-state refutation. The negative intentionally constructs an unreachable malformed state; it is not a live exploit.
4. `ControlStack/Deployment/NamedContracts.lean`: named-field views for all 21 `TrustedBroker.Allowed` conditions and the seven `BaseAccepted` and six `WritersChecked` conditions, plus bidirectional `↔` lemmas. `Deployment.Accepted` already had six named fields; its full view is also proved equivalent. Existing definitions and enforcement are unchanged.
5. `ControlStack/Core/RefinementTransfer.lean`: generic model-to-model list-trace forward simulation. `ControlStack/Scenarios/SC25RefinementReuse.lean` proves SC-25's `simulation_run` statement from this lemma (`simulation_run_via_transfer`, and `simulation_run_agree` shows both proofs state the same fact). `SC25Refinement.lean` itself is **unchanged**, because its SHA-256 is pinned in `scenarios/SC-25/manifest.json` (recorded kernel check). Existing AuthInstancesA/B already use `AuthenticatedLog.issued_trusted`; scenario gate clients already use `Core/Gate`, so further abstraction without a demonstration of redundant theorems would add unnecessary proof obligations. Other refinement/liveness cases have varying state and fairness assumptions and are **not** claimed identical.
6. T4.2: retain all three countermodels of false literal acceptance monotonicity and only the narrow `accepted_path_safety_monotone` property. No attempted proof of the false claim.
7. CI/reproducibility: full root `lake build` and new Lean targets added to `deployment-release.yml`, generated registry and source-normalized catalog updated; English deployment summary and deployment claim corrected.

## English / one-to-one comparison status

- Changed G0 `Accepted` explanation: previously “broker and receiver share UID *only if*” (weaker than Lean); now explicitly **if and only if**. **Old G0 `Accepted` verdict is stale for the revised English input.** It must be rechecked strictly blind.
- The deployment overview gains a **supplementary** model provenance explanation, but `deployment_broker_safe` itself is unchanged: its tested conclusion remains a used approval, not exactly-reviewed bytes. The old G0 formal comparison targeted that unchanged theorem and does not verify the new supplementary claims; review the changed explanatory text independently.
- No original 187 theorem statement or translation block changed its conclusion. `SC25Refinement.lean` is byte-identical to `main` (an earlier revision of this PR refactored `simulation_run` in place, which broke the pinned SC-25 hash and `check_scenarios`; that was reverted and the reuse moved to a bridge file).
- The new support theorems (`Provenance`, `NamedContracts`, `RefinementTransfer`) have **no strictly blind English↔Lean one-to-one results**. The historical G0 comparison of 26 headlines was not strictly blind (19 equivalent, 2 weaker, 3 stronger, 2 undecided before this edit). G1–G7, 161 claims, were never checked; do not award any badge.

## Build, gates, and what NOT to conclude

A draft PR is **not** a green test receipt. The CI jobs for the current branch perform the Lean checks and static Python deployment tests, including the differential suite (~12 minutes). The connected GitHub checks must be inspected on the final commit and failures resolved before merge; **queued, skipped or unrun is not PASS**. Standard axioms only, no `sorry` or `native_decide`. Frozen paths (`ControlStack/EgressGate.lean`, `prereg/`, `ledger/`, `proofs/`, evidence and archived runs) were left unchanged.

**Not verified by this document or its authoring:** faithful real-world extraction, authenticated OS identity, exact Python-to-Lean refinement, historical exact-byte file provenance, human review, new independent held-out sets, the G1–G9 resources, real agent runs, or the deferred researcher-friendly presentation. Python checks and Lean kernel gates only count once CI records actual passing outcomes.
