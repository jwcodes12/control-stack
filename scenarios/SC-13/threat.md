# SC-13: Trusted monitoring and audit dispatch

**Bad event:** A workflow effect is dispatched without its trusted audit record, or an agent disables that audit path.

**Adversary:** App-role attacker can request dispatch and mutate unprotected app state, but cannot directly invoke a real independent effect broker under the modeled hypothesis.

**Boundary/scope:** PostgreSQL test dispatcher record ordering, not all workflow effects or completion-time auditing.

**What would refute the claim:** Invoke workflow execution outside trusted dispatcher or show audit/effect mismatch or unauthorized dispatcher credential exposure.

Relevant families: F1, F3, F4. The manifest is an evidence ledger, not a deployment certificate.
