# SC-19: candidate formal claim

**Scope:** Each protected mutation occurs only after a transaction/preview gate with a recoverable prior state.

**Families:** F1, F3, F4. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Cause a side effect through a second channel or show restoration is impossible.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
