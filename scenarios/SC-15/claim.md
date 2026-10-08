# SC-15: candidate formal claim

**Scope:** Restricted security-sensitive surfaces cannot change or ship without a pinned reviewer authorization; no claim of all-backdoor absence.

**Families:** F1, F3, F4, F6. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Introduce a malicious behavior outside the protected surface or through generated artifacts.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
