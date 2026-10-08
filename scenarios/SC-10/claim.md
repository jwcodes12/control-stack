# SC-10: candidate formal claim

**Scope:** Any protected rule-set change requires exact-diff authorization before effect.

**Families:** F1, F3, F7. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Mutate rules through an alternate API, helper daemon or unbound approval.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
