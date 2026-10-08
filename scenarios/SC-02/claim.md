# SC-02: candidate formal claim

**Scope:** If every message in one receiver lineage is charged against an atomic durable lifetime budget and no rollback is possible, cumulative views remain bounded.

**Families:** F2, F3, F8. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Run parallel writers or restore a ledger snapshot and obtain more than the declared lifetime transmissions.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
