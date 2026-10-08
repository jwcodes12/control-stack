# SC-11: candidate formal claim

**Scope:** The resolved path and mount identity of every permitted write excludes trust roots.

**Families:** F1, F3, F4. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Exploit symlink swaps, bind mounts, alternate path resolution or inherited file descriptors.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
