# SC-23: candidate formal claim

**Scope:** Tool permissions remain tied to trusted user intent and exact authorized transaction identity, not untrusted text.

**Families:** F1, F3, F7. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Feed a malicious tool result and induce a privilege-bearing action outside original authorization.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
