# Independent review form — SC-01 and reusable control primitives

**This is a blank review instrument, NOT a completed or signed review.**
Do not fill on behalf of another reviewer or promote theorem statuses without their
actual judgment and reproducible reference material.

- Reviewer and independence/conflict disclosures:
- Repository commit hash and pinned Lean toolchain:
- Source list / evaluated exact theorem declarations:
- Reproduction commands, logs and failure notes:
- Fully elaborated Lean goal (quantifiers, typeclasses, universes, hidden definitions):
- Claimed real-world catastrophe event and observables:
- Counterexample search for vacuous or narrower-than-intended theorem statements:
- Whether the theorem's premises imply all claimed consequences:
- Which assumptions are encoded as axioms versus theorem hypotheses:
- Whether representation gaps remain (kernel law, channel alphabet, timing, schedule, OS, host, side effects):
- Explicit unsupported contexts / adversary classes:
- Disposition: PASS MODEL STATEMENT / NEEDS AMENDMENT / FAIL / INCONCLUSIVE
- Conditions to apply result to a specific deployment:
- Date, reviewer-supplied signature or external report link:

Minimum review targets: `SafetyCaseSC01.sc01_case`,
`GatewayCore.core_bound`, `GatewayCore.refusal_blanks`,
`Leakage.covert_seq_seed`, `Leakage.audit_leak_bound`,
`HaltLiveness.liveness_if_delivered`, `GateClients.Approval.approval_safe`,
`Lease.lease_safe`, `PolicyTamper.policy_preserved_if_protected` and
`GateComposition.shared_invariants`.

Reviewer must explicitly test whether the model includes **all** receiver-visible
variables over the entire secret lifetime, and distinguish result validity in
Lean from runtime correspondence or a useful/hardened deployed application.
A satisfactory report must cite the actual theorem type, not merely the
theorem name or proof-compilation status.

**Submission gate:** retain source-only status until a genuinely independent
reviewer supplies their own reproducible review. A model-generated self-review
by the author is not an independent attestation.
