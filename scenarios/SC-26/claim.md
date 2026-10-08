# SC-26: candidate formal claim

**Scope:** A single-use authorization bound to exact payload, recipient, scope and expiry must precede the transaction.

**Families:** F1, F3, F5, F7. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Replay approval or change a recipient, amount or authority after signing.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
