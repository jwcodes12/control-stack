# SC-06: candidate formal claim

**Scope:** If all cross-agent reads and writes pass typed canonicalized mediation, forbidden persistence transitions are absent in the model.

**Families:** F1, F2, F3. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Make a later agent read an unmediated writable path or memory store.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
