# Release-time provenance: design decision required

**STATUS (2026-10-12): Option A chosen by the owner ("event log"); a model-only prototype is implemented in `ControlStack/Deployment/ReleaseLog.lean` and `ReleaseLogWitnesses.lean` (section "Prototype" at the end). Options B and C are NOT implemented.**
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

## Prototype (Option A, model only)

**Semantics chosen for the prototype (the narrowest, and an open question for the owner):** a *logged release* is exactly one broker `release` step, i.e. the broker's committed transaction that admitted the request. It is **not** "the receiver received the bytes" and **not** "durably published". The other two meanings the decision above asks about (received, durably published) are not modeled; there is no publish receipt.

What is proved (all compile with `lake build`; standard axioms only; no `sorry`):
- `LStep`/`LTrace`: the log is extended by exactly the `release` steps. `lstep_forget`, `ltrace_forget`: every logged step projects to an existing broker `Step`, so the log constrains nothing the broker can do. `lift_step`, `lift_trace`: conversely every broker trace has a logged shadow (conservative extension).
- `LogSound` (`ltrace_logSound`): the log's nonce list equals `consumed`, its costs sum to `spent`, its length equals `releases`. Hence nonces in the log are unique, via `Safe`.
- `ltrace_log_extends`: append-only (a later log extends the earlier one with newer events).
- `release_event_matches`: at the instant of release the event holds the *approved* digest and destination, equal to the request's, the signer is an approver, the agent an agent, the cost positive. `ltrace_logAuthentic` adds the reviewer's role (from `ReviewProvenance`).
- `release_nonce_new_in_log`, `no_duplicate_release_event`: no nonce is logged twice. `halted_no_new_events`: no event after HALT.
- `deployment_release_events`: for a `BrokerProtocolRefinement`, every published nonce has a release event with the role and cost facts. This is the release-time statement the design asked for, **under the existing refinement premises** (publication sublist, extraction faithfulness, runtime correspondence).
- Witnesses: a concrete logged trace (`logged_trace`, `event_fields`), the replay and the tampered artifact each emit no event, and `admitted_not_published` shows a logged release with an empty publication list. A logged release is not evidence of publication.

What is **not** done: crash between admission and publication, retry/idempotence at the receiver, publish receipts, rehashing of live bytes, an explicit false-extraction countermodel, runtime persistence of the log (transactional event persistence in the broker, extractor support, an OS receiver witness), log custody and rotation, and the independent human statement-fidelity review. Nothing here changes `trusted_stack`, the broker's `State`, or any pinned file, and `deployment_broker_safe` is unchanged.

**No runtime implementation of any option is authorized by this document.**
