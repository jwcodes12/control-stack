# SC-03: candidate formal claim

**Scope:** Every actual outbound send by a confined process must have an earlier valid permit to a pinned destination.

**Families:** F1, F3. **Adversary label:** adaptive-feedback.

**Proof source:** `ControlStack/EgressGate.lean` (existing model theorem(s); retain imports; see legacy manifest for exact theorem names).

**Premises:** All relevant actions/effects and observations are mediated; trusted state cannot be rewritten by the attacker. Scope must be independently checked.

**Necessity witness / counterexample:** Observe an unattributed packet, inherited socket bypass or host deputy exfiltration.

**No-go:** This is narrower than a proof that an arbitrary AI cannot cause the general harm. A theorem checked under these premises does not establish them in a deployed system.
