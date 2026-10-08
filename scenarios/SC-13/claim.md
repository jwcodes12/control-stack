# SC-13: candidate formal claim

**Scope:** When every workflow effect is dispatched by an independent gate, a trusted audit record precedes dispatch.

**Families:** F1, F3, F4. **Adversary label:** adaptive-feedback.

**Proof source:** `ControlStack/AuditDispatch.lean` (existing model theorem(s); retain imports; see legacy manifest for exact theorem names).

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Trigger a workflow effect through a path bypassing the dispatcher, or forge/drop the trusted audit record.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
