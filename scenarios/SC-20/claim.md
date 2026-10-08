# SC-20: candidate formal claim

**Scope:** Only content-addressed approved dataset versions can be consumed; semantic purity is not implied.

**Families:** F1, F3, F4, F6. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Train on an unreviewed shard or inject harmful samples into approved input.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
