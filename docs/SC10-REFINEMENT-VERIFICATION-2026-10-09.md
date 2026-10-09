# SC-10 refinement verification ledger (draft, 2026-10-09)

Source base: `37e118ecfb5c923d94edd15100fc867fd8ab32da`.
Relevant frozen reference sources: `scenarios/SC-10/harness/store.py`,
`run_sc10.py`, `ControlStack/Scenarios/SC10Policy.lean`, and
`prereg/SC10-POLICY-STORE.md`.

This is a **review/verification ledger**, not runtime conformance evidence.

## What the new candidate proves, if Lean CI passes

`ControlStack/Scenarios/SC10Refinement.lean` defines a separate event-machine state and
transitions for a policy store, decisions, builds and HALT, plus an abstraction to
`SC10Policy`. It attempts one-event and trace simulation, transfers the existing
`SC10.sc10_safe` invariant, and compares fresh versus cached enforcement after
policy tightening. It deliberately does not postulate safety of the concrete trace.

All abstract decisions correspond only to *recorded* enforcement decisions. A
separate completeness statement for every **actual enforcement effect** is needed.
The `alpha` map's equality of recorded lists cannot establish that unrecorded effects
do not exist. The proof uses `SC10.Dec` as an observation type; its fidelity to
emitted JSON and to the actual accepted/denied effect must be checked separately.

## Critical source-level incompatibility: non-atomic read/use

The deployed reference PEP in `scenarios/SC-10/harness/pep.py` performs one
`rpc(... latest ...)`, then separately evaluates the policy and writes the
receipt. The Lean `SC10Policy.step(.decide)` and
`SC10Refinement.stepC(.enforce)` combine that read and use into **one atomic
step**. Therefore their trace simulation is NOT a proven simulation of
arbitrarily concurrent PEP/store execution.

`ControlStack/Scenarios/SC10ReadUseGap.lean` provides a model-level
distinguishing witness: an admin write can occur between `readLatest` and
`apply`, yielding an applied decision at version 0 when the latest version
is 1. This is an executable Lean counterexample to the broad atomicity
assumption, **not** evidence that the frozen preregistration experienced the
race. Treat SC10 runtime correspondence as **BLOCKED BY UNMODELLED READ/USE
INTERLEAVING**, not merely unverified. A future hardened evaluator would need
an agreed linearization point at the actual effect, version revalidation or
serializable store/effect locking, followed by new source-pinned, separately
preregistered tests. Editing the frozen harness in place is prohibited.

An independent negative regression in
`tools/test_sc10_restart_gap.py` also exercises a second boundary: the
unchanged reference store's append log survives a process restart while its
active in-memory versions restart empty. The CI run for that regression
has not yet been validated; this file does not claim an observed execution.

## Open and falsifiable implementation premises

| ID | Requirement | Proposed falsification |
|---|---|---|
| SC10-R1 | `SO_PEERCRED` pids cannot be impersonated by an untrusted principal; the admin PID, process lifetime and credentials are securely bound | Spawn/reuse pid, attempt same-UID compromise; document whether the security boundary is only pid equality |
| SC10-R2 | All policy mutations pass through the sole protected store; there are no direct firewall, file, environment, namespace or policy-source bypasses | Enumerate enforcement APIs, alternate paths and writable filesystem mounts; try each without store authorization |
| SC10-R3 | The store read/write order has a valid linearization point, including simultaneous clients | Inject concurrent writes, reads and decisions and compare each decision's recorded version with the most recent committed admin version *at the effect time* |
| SC10-R4 | The two-record disk write, fsync, in-memory append and restart/recovery code retain append-only meaning after crash or partial write | Terminate between log write, fsync, commit stamp and acknowledgment; restart, recover and compare the accepted store state against durable log |
| SC10-R5 | No stale decision is applied between checking latest and executing an enforcement effect | Delay or pause the evaluator after reading; update policy; observe whether the old decision still takes effect |
| SC10-R6 | Every build executes the exact approved bytes at a protected pinned path, not a race-swapped path, interpreter, fd, symlink or mutable library | Replace inputs between digest/read and execution; test symlink, PATH, interpreter and shared-library bypasses |
| SC10-R7 | HALT is not merely a receipt; it prevents every downstream effect, including concurrent work and pre-HALT in-flight actions | Race HALT with accepted decision/build and inspect external effects rather than just the log |
| SC10-R8 | Errors, malformed messages, disconnects and permission failures never fall back to permissive enforcement | Fuzz framing and JSON, truncate replies, force socket failure, restart workers and verify fail-closed |
| SC10-R9 | Exact JSON receipt fields, version indexing and digest encoding correspond to Lean constructors/values | Differential replay of all event cases and state snapshots; require a counterexample to fail when fresh/admin-only/single-evaluator/pinned flags are disabled |
| SC10-R10 | Admin-authored policies are actually correct for the intended security property | Independent semantic review; being admin-signed is not itself policy correctness |

## Acceptance gates before scenario registration

1. CI must build the candidate module with standard axioms only; inspect
   `#print axioms` rather than trusting a source-only registry.
2. An independent reviewer must check the elaborated Lean statement and whether
   every branch of `stepC` honestly abstracts the runtime.
3. Differentially compare parser/store/evaluator/build traces against the concrete
   machine, including rejecting, racing, crashing, replaying and alternate paths.
4. Pin runtime source hashes and verify existing evidence/prereg hashes unchanged.
5. Only then register the theorem in `manifest.json`, `claim.lean` and
   `TrustRoot.lean`; explicitly retain `implementation_conformance` as unresolved.
6. Do not elevate SC-10 above CONDITIONAL or mark deployment assurance without an
   independent, authorized deployed enforcement test and usefulness evidence.

This checklist is deliberately narrower than the completed refinement backlog:
this draft does not discharge any of these runtime/environment roots.
