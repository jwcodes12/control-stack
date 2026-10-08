# SC-09: candidate formal claim

**Scope:** Every agent-reachable transition preserves the declared privilege lattice unless a separate trusted principal authorizes it.

**Families:** F1, F3. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Use an alternate identity switch, inherited capability or indirect service to gain privilege.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
