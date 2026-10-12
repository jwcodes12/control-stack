# Release-time provenance: design decision required

**DESIGN ONLY. DO NOT IMPLEMENT UNTIL OWNER APPROVAL.**
Model-written/model-reviewed; there has been no independent human review.

## Unclosed property

`TrustedBroker.State` records `releases : Nat`, total `spent`, consumed nonces,
retained approvals/leases, an artifact-presence flag and `intact` boolean by
*digest*. `committed` increments counters and marks the approval used, but
stores **no immutable release record** containing nonce, digest, destination,
content hash, observed output path, or durable publish receipt.

The current `Provenance.deployment_broker_provenance` relates a published nonce
to its *current retained approval* and current review/lease information.
It cannot express, let alone prove, that the exact bytes and destination
written at a given release matched what was signed and approved **at the
release time**. A mutable review entry can be overwritten; the abstract
`intact` flag is an assumption about the concrete SHA-256 recheck, not a
byte-level proof. `BrokerProtocolRefinement.publication` is a sublist
relationship, not an attested per-output digest or destination.

## Option A — Separate append-only ReleaseLog with refinement (recommended)

Add a new `ControlStack/Deployment/ReleaseLog.lean` containing
`ReleaseEvent` with nonce, approved digest, destination, agent UID, lease
identifier, signer, reviewer, cost and an abstract publish receipt. Define
`LoggedState` as `TrustedBroker.State × List ReleaseEvent` with every
recorded `release` step atomically extending the log and a projection
`forgetLog : LoggedState → TrustedBroker.State`. Prove a forward simulation
that **each logged transition projects to an existing broker `Step`**;
prove `log.length = releases`, unique nonces and event-time
digest/destination equality at the point of release. Later, a distinct
bridge can bind a release event to an actual receiver receipt and rehashed
content.

* Cost: one additive model, an induction over logged transitions, agreement
  witnesses and explicit environment/refinement premises. The runtime
  needs transactional publication-event persistence, extractor support,
  tests and a witness from real execution before a deployment claim.
* Preserves: historical broker `State` API and all pinned theorem source
  bytes; existing `Safe`, `Coherent` and trace results remain untouched.
* Limitation: a model-only log still does not certify live filesystem
  bytes or publishing side effects without additional trustworthy capture,
  atomicity and anti-rollback assumptions.

## Option B — Add events directly to TrustedBroker.State

Extend `State` with an append-only `releaseLog` and modify `committed`,
`initial`, trace constructors and invariant proofs to maintain a
per-release digest/destination relation. This is convenient for a single
state theorem, but every current constructor, record update, witness,
fixture, serialization bridge, and all proof clients may need repair.

* Cost: high invasive migration; regenerates proof dependency outputs,
  changes the abstract state used by many scenarios, and likely requires
  changes to SHA-pinned scenario files or frozen evidence that this PR
  **must not modify**.
* Risk: incompatible with the current frozen-source and release-gate
  constraints. Requires a separate owner-approved, newly pinned protocol
  version and full live regression; not acceptable as a cosmetic cleanup.

## Option C — External signed release receipts only

Leave the broker state unchanged. Build a receiver-side, tamper-evident
append-only journal containing nonce, digest, destination, observed output
hash, storage version, time and signing identity. Audit it against broker
commit history and prove a model relation to abstract releases.

* Cost: lower Lean-state disruption, but substantial OS/I/O testing:
  fsync ordering, crash recovery, reconciliation of admitted-but-unpublished
  requests, key custody, rollback prevention, handling missing or double
  receipts, and legitimate retry semantics.
* Risk: external receipt integrity alone does **not** prove that the
  receiver wrote the approved bytes unless the observation/attestation
  boundary is specified and independently evaluated.

## Decision and acceptance tests

**Recommend Option A**, followed by an optional Option C runtime receipt
bridge. Keep the old broker theorems as conditional, model-only assertions.
Before implementation obtain the owner's decision on whether a logged
`release` means *authorized/committed*, *receiver received*, or *durably
published*. These differ under crash, retry and HALT. Define the idempotent
transaction boundary, bytes-to-digest semantics, exact destination naming,
log custody and rotation, and acceptable delayed-publication policy.

A release-log prototype should demonstrate: one successful admitted-and-
published event; one unapproved/tampered request that emits no record; a
crash between admission and publication; duplicate nonce/retry behavior;
HALT in flight; and an explicit false-extraction countermodel. Require
`lake build`, standard-axiom audit, pinned-source preservation, generated
registry checks, Docker/OS receiver witness and an **independent human**
statement-fidelity review before claiming real release-time provenance.

**No implementation of any option is authorized by this document.**
