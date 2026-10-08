# SC-25: candidate formal claim

**Scope:** Every irreversible effect is gated by a prior valid decision and shutdown forbids further effects.

**Families:** F3, F6. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Observe an external irreversible effect followed by a late flag.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
