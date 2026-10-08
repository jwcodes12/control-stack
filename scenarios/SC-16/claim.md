# SC-16: candidate formal claim

**Scope:** Every deploy consumes a reviewed exact artifact hash and approval scoped to the target.

**Families:** F3, F4, F7. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Ship via a bypass route or substitute bytes between review and deployment.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
