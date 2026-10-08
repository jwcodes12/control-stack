# SC-22: candidate formal claim

**Scope:** Reported numerical claims can be traced to immutable data and reproducible computation; semantic validity remains external.

**Families:** F4, F6. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Recompute the same artifacts but find that the substantive interpretation is false.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
