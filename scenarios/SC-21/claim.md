# SC-21: candidate formal claim

**Scope:** Evaluator and benchmark bytes match frozen approved hashes and scoring is computed independently.

**Families:** F3, F4, F6. **Adversary label:** adaptive-feedback.

**Proof source:** None; thin Lean goal pending, not verified.

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Alter a runtime dependency, silently skip a sample or tamper with telemetry.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
