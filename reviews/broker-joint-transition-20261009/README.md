# Broker joint transition continuation — 2026-10-09

Resumed from GitHub `main` at `083874048518b68d754f0c392ad0cb84f01174ba`
after its root `completed.md` appeared. The original local checkout and its
untracked work were left intact; this work uses a separate checkout.

## Delivered

`ControlStack/TrustedBroker.lean` models committed stage, review, lease issue,
approval, revocation, release and HALT transactions in one shared state.
Denied requests, reads and reopening persistent state are identity transitions.
Ten declarations prove initial invariants, joint quota/release-count/nonce
invariants over arbitrary transaction traces, absorbing HALT, immediate nonce
replay rejection, and coherence of a ghost nonce history with concrete approval
used flags. The history check is redundant for coherent reachable states.

The only effect is a SQLite release row. The model abstracts parsed UID/token,
destination and digest/body identities as naturals. Artifact integrity is an
explicit predicate for the Python SHA-256 recheck. Trusted review asserts review
identity; it does not assert harmless content. A trusted store must linearize
committed transactions without rollback. Transaction ordering models concurrent
commit serialization, not asynchronous OS effects or failure halfway through an
external deployment. There is no universal Python/SQL-to-Lean refinement proof.
The model permits denied requests even when an action could have been accepted;
it is a safety relation, not a usefulness specification.

`trusted_stack/test_transition.py` supplies an independent in-memory admission
oracle. It compares every table after each attempted transaction in 64 seeded
histories (4,544 transitions), plus 72 targeted transition checks. It covers
multiple agents/leases/nonces, wrong roles and exact payload bindings, expiry
boundaries, global and lease caps, revocation, reopen, HALT and clock rollback.
Separate tests reject caller-selected broker cost and corrupted reviewed bytes.
These finite tests are evidence about the implementation, not a universal proof.

The live socket test now exercises eight malformed callers that disconnect and
one valid release whose acknowledgment is lost. A trusted subsequent read sees
the committed row; retry is refused. The server previously propagated a failed
reply write and exited; it now keeps serving. The library also explicitly closes
bootstrap and failed-open database connections.

The mutation runner works only in temporary copies. It rejects seven weakened
variants: missing global cap, lease cap, approval expiry, revocation, HALT,
artifact integrity, and the former disconnect crash. CI runs the reference,
live identity, mutation and pinned full Lean checks.

## Validation and limits

- 22 reference Python tests passed, including the new transition oracle.
- 14 acknowledged live Linux peer-credential requests plus 9 disconnected
  requests passed; exactly one SQLite release row was committed.
- Seven weakened variants were rejected by assertion or observed broker loss.
- Pinned Lean 4.34.0 full `lake build ControlStack` passed. All ten new printed
  axiom reports use only standard axioms. `Print.lean` obtains elaborated model
  definitions and theorem types; it is not independent expert review.
- Existing gateway correspondence, receiver-boundary, gateway, lifetime,
  scenario/oracle, certifier, metadata mutation and VM configuration tests
  passed. The saved VM receipt verifier retained its failed usefulness gate.
- All 28 scenario claim files compiled with standard-only reported axioms.
  The original SC-01 case checker passed its 48 case and 38 supporting theorem
  checks, 20 source bindings, differential checks and receipt verification; it
  returned the expected exit 3, **HYPOTHESIS_REFUTED**, preserving the historical
  shared-cache observation refutation. This is not a safety pass.
- Generated registry/catalog/index drift checks are required after the new
  declarations. The current registry has 875 source-indexed declarations;
  the 821 existing UNKNOWN classifications remain unpromoted.

Exact final command results and file hashes are recorded in `validation.json`.

## Host gate and next work

Read-only preflight: this host is aarch64 with two CPUs; QEMU binaries are
available, but `/dev/kvm` is absent. **G0 = BLOCKED_HOST.** No new guests,
deadline amendment, usefulness trial, side-channel probe, production effect or
deployment-assured status was introduced. The historical 0/64 baseline and
mediated VM lifetimes remain failed evidence.

Next VM work is the independently pinned native guest port and G0–G4 sequence
in `VM-HANDOFF.md` on an authorized native KVM host. Next broker work is a
formal database-state extraction/serialization refinement, followed by a
separate actual-effect adapter with crash/HALT semantics, trusted metering,
anti-rollback state and time. F6 imperfect adaptive auditing and independent
human theorem review also remain open. Scenario assurance statuses are unchanged.
