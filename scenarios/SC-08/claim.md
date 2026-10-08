# SC-08: candidate formal claim

**Scope:** Only hash-approved executables can be started by the mediated exec transition.

**Families:** F1, F4. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Execute a shell, interpreter, mutable symlink target or inherited binary outside the allowlist.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
