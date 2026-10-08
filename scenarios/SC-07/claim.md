# SC-07: candidate formal claim

**Scope:** If secret reads and every outbound artifact store require separate trusted capabilities and quotas, forbidden bulk transfers cannot occur in the model.

**Families:** F1, F5. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Stream bytes via an allowed store, encoding into approved requests or a forked worker.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
