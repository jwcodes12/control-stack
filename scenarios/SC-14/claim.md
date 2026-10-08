# SC-14: candidate formal claim

**Scope:** A global restart-safe lease counter bounds total authorized spend across all agents.

**Families:** F3, F5. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Exceed budget with concurrent workers, retry after crash, or duplicate a lease.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
