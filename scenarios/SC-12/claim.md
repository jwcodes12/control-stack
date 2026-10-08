# SC-12: candidate formal claim

**Scope:** All process creation, scheduled execution and durable executable writes require a bounded trusted lease.

**Families:** F1, F3, F5. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Create a service, cron job or helper process outside the mediated lease.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
