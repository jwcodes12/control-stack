# SC-28: candidate formal claim

**Scope:** All instances use one serializable durable counter and preserve the aggregate bound.

**Families:** F3, F5, F8. **Adversary label:** multi-agent-persistent.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Spend twice via races, split identities or rollback.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
