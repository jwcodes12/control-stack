# Shared-state gates and policy tampering — source-level extension

**Not kernel-replayed during this documentation-only change.**
No claim about real-world Linux policy immutability, SQL correspondence, or a
complete composition theorem for EgressGate and AuditDispatch is made here.

- \`ControlStack/PolicyTamper.lean\` introduces an explicit
  \`attackerCanWrite\` capability. The integrity statement requires it to be
  false; the positive witness shows a one-step policy replacement when true.
  This repairs the *specification visibility* of EgressGate's earlier
  \`tamperPolicy => s\` idealization, not its host implementation.
- \`ControlStack/GateComposition.lean\` uses one shared state and demands
  that every joint action preserve *both* invariants. An intentionally unsafe
  trusted-deputy transition bypasses a second gate's approval bit.
  To instantiate this result, a future composition theorem must map all
  concrete egress, dispatch, crash, attacker and deputy effects into that shared
  state and prove the transition hypotheses.

**Falsifiers:** edit trusted rules through a writable mount/FD, replace the
policy after launch, privileged host deputy makes requests on agent-controlled
data, crash/restart resets authoritative gate state, or source evidence no longer
matches the compiled binary. These remain deployment obligations.

**Next proof tasks:** instantiate shared invariants for pinned peer effect
AND audited dispatch effect; specify atomicity and time of both checks; prove
a pre-effect veto path and absorbing halt under a separately stated fairness
schedule. Fairness/liveness and the leakage/audit small completions have **not**
been proved by this change.
