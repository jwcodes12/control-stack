# SC-17: candidate formal claim

**Scope:** Every apply to the modeled resource graph preserves a declared deny constraint.

**Families:** F1, F3, F4. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Issue an unmediated apply or exploit resource kinds missing from the graph.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
