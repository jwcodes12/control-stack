# Bounded transition-model differential coverage

Source-only model parity check; it does **not** prove runtime correspondence.

`python3 tools/bounded_model_diff.py` generates deterministic Lean propositions and checks them with pinned Lean's kernel using `by decide`. Each expected result is computed by an independently implemented Python shadow transition machine, not copied from Lean outputs. Finite exhaustion includes all words of length 0–2 over each scenario's explicit operation alphabet, plus longer causal chains. The compared projections include recorded effects, authorizations or expiry, and HALT state.

- **SC-06**: issuer, exact-entry confirmation, replay, wrong reader/value, independent approvals, HALT; the checked `scoped_safe` theorem still presumes typed ingestion, authenticated user events, and complete mediation.
- **SC-08**: digest allowlist, interpreter script selection, writable/noexec mounts, path/content replacements, HALT; this checks the idealized transition, *not* Linux `execve`, descriptor provenance, or same-UID isolation.
- **SC-25**: pre-effect digest audit, trusted approval for classified irreversible content, stale checks, amendments, timeout, crash, HALT; no real executor or audit credentials are validated.
- **SC-26**: use the existing full-state `scenarios/SC-26/harness/lean_difftest.py`; it checks sampled Python model vs verbatim Lean source, not external bank effects.

Run:
```bash
lake exe cache get
lake build ControlStack.Scenarios.SC06OneUse ControlStack.Scenarios.SC08Exec ControlStack.Scenarios.SC25Audit
python3 tools/bounded_model_diff.py
python3 scenarios/SC-26/harness/lean_difftest.py -n 200
```

The additional CI workflow triggers on both the executable shadow models and their Lean counterparts. Tests reject semantic disagreements but do **not** imply that a live Python harness, kernel mediation layer, cryptographic identity, durable receipt, OS process, or payment system implements the formal transition semantics. Independent human theorem-statement fidelity reviews and VM tests are still required.
