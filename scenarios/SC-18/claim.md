# SC-18: candidate formal claim

**Scope:** Every admitted serving configuration meets a machine-decidable logging invariant.

**Families:** F1, F3, F4. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Load a shadow config or mutate runtime monitoring after admission.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
