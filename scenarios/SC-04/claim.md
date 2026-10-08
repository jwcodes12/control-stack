# SC-04: candidate formal claim

**Scope:** If all receiver-visible diagnostics/timing are constant or included in a finite observation alphabet, the full transcript bound counts them.

**Families:** F2, F3, F8. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Encode a secret bit through a diagnostic exit code, page-cache timing or heartbeat arrival.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
