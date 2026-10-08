# SC-27: candidate formal claim

**Scope:** An independently rooted attestation chain must bind source, evidence, checks and review decision before a case is relied upon.

**Families:** F3, F4. **Adversary label:** multi-agent-persistent.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Alter a hash and its manifest together, or substitute a forged CI attestation.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
