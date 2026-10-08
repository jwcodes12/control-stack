# SC-01: candidate formal claim

**Scope:** For a complete receiver-visible view with certified cardinality or bounded side-kernel domination, exact recovery is bounded by view mass / 2^32.

**Families:** F2, F8. **Adversary label:** shared-seed-side-observing.

**Proof source:** `ControlStack/SafetyCaseSC01.lean` (existing model theorem(s); retain imports; see legacy manifest for exact theorem names).

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Any non-transcript receiver-visible shared-cache/timing signal above the certified side mass refutes the gateway-only premise.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
