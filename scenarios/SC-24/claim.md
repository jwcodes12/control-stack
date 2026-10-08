# SC-24: candidate formal claim

**Scope:** Under a complete-view test game with declared law domination and conditional recall, uncaught risk obeys the stated bound.

**Families:** F2, F6, F8. **Adversary label:** shared-seed.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Produce an attacker strategy outside coverage or a monitor state side channel invalidating the premises.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
