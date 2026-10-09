# Receipt-verification layer: precise claim boundaries

This branch adds `ControlStack/Core/CheckedTrace.lean` as **source-only** work toward the eleven remaining scenario refinements.

## What is proved

A receipt includes `before`, `op` and `after`. The executable validator recomputes the exact Lean transition `step before op`, rejects a wrong predecessor, rejects a wrong successor, and threads state across the entire ordered sequence. The general `verified_sound` theorem states that any accepted finite sequence has the same final state as formal replay.

Corollaries transfer existing safety statements to accepted receipts for **SC-06, SC-08, SC-09, SC-10, SC-14, SC-15, SC-17, SC-19, SC-20 and SC-23**. SC-04 separately receives an exact finite alphabet cardinality statement for typed canonical logs. The generic checker has accepted and rejected one-step nonvacuity tests.

## What is *not* proved

- A malicious agent can omit or fabricate a receipt; acceptance does **not** establish exhaustive logging, trustworthy identity, checked-before-effect delivery, or the absence of bypass effects.
- A Python or Linux harness has not yet been instrumented to produce genuine complete-state receipts; no replay of recorded runtime evidence is claimed.
- The concrete event machines are still not independently specified and shown to refine the abstract operations; this is not a replacement for SC-07's concrete gateway simulation.
- Side observations including timing, kernel state, caches, filesystem hard links and out-of-band cloud side effects remain outside these certificates unless included in the trace.
- In SC-04, cardinality of typed records does not establish that every real receiver observation fits the alphabet; the statistical conditions of `ChannelInstances.log_channel` remain explicit.

## Remaining implementation requirements (per scenario)

1. Define a separate, independently reviewed concrete event type from genuine runtime syscall/API semantics.
2. Define a total and fail-closed decoding from observed events to the existing abstract operation and state; bind every effect and every source identity.
3. Require complete trusted recording or check-before-effect mediation, identify unobservable effects, and exercise negative bypass controls.
4. Prove a non-circular forward simulation and transfer the corresponding safety property; if the model excludes a dangerous effect, keep that exclusion as a named premise.
5. Re-run frozen evidence on controlled disposable infrastructure under a preregistered test and verify input, executable, kernel, policy and environment hashes.
6. Only then update each scenario manifest's `model_runtime_correspondence`, add its own refinement edge to TrustRoot, regenerate the ledgers, and request independent English–Lean fidelity review.

**Do not mark any of the eleven scenarios complete on the basis of the transcript theorem.** It is a reusable, independently replayable checking primitive, not real-runtime assurance.

## Reproduction note

The generated theorem registry and normal-form statement catalog are source-only inventories; the separate GitHub Actions Lean job must successfully elaborate the proof statements and show their permitted axiom dependencies before this layer can be merged.
