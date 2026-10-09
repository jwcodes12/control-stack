# SC-06 tightened reference model: context IDs and single-use confirmation

This is a **source-only alternative**, not a revision to preregistered SC-06
evidence or a claim that the existing Python harness implements these rules.

## Why this exists

The original `SC06Artifacts.lean` has two specification-fidelity gaps, now
kernel-checked in `SC06ConfirmationReuse.lean` (PR #26):

1. `ActOk` only asks whether a matching confirmation exists. It does not
   consume it, so the model admits two sensitive effects using one approval.
2. `ctxOf` matches by (agent, numeric value). Equal values with different
   provenance can be conflated; the source of the chosen value isn't the
   source of every real-world derivation of that value.

## New machine and safety theorem

**Approval-time existence check (2026-10-09 repair):** The `confirm` transition requires an existing append-only context entry whose ID, reader, foreign writer and value match the proposed approval. A user event cannot pre-authorize an entry that will be ingested later. At `act`, the entry and one-use confirmation are checked again.

The Lean file now includes kernel-checked `example ... := by decide` negative/positive controls: premature confirmation is not stored, future ingestion cannot activate that confirmation, a mismatched value fails, and correct post-ingestion confirmation permits one effect. Anonymous `example` declarations are intentionally not registered as named theorems.

**Remaining premise:** In runtime, trusted ingestion, immutable and non-reusable entry handles, authenticated human approvals, complete effect mediation, causal ordering and receiver-side effects remain unproved.

`ControlStack/Scenarios/SC06OneUse.lean` defines its *own* state and events.
The trusted ingress event allocates context entry IDs; an authenticated user
confirmation binds an **exact** (reader, tool, entry ID, value) tuple; a
sensitive cross-agent effect must match both the entry and the confirmation.

The `scoped_safe` theorem is intended to prove over **arbitrary finite
traces** that every such recorded effect has a valid, trusted-user-issued
confirmation matching its source entry and that effect confirmation IDs
are pairwise distinct. The guard is applied in the **same abstract step**
that adds an effect. The proof uses a step-preserved invariant, then induction
over traces. The theorem must pass pinned Lean CI and an independent
statement-fidelity review before use as assurance.

There are three named theorem controls plus additional kernel-checked `example` controls:
- a second action cannot spend the same confirmation twice;
- approving one entry ID cannot authorize an equal-value different entry;
- an honest foreign sensitive action is still achievable.

## Explicit assumptions and non-goals

- This model only tracks **cross-agent, sensitive** actions. Local actions and
  non-sensitive operations, derivation chains, tool results, alternate stores
  and downstream irreversible external effects are not modeled.
- Every `ingest` event is presumed to originate from the trusted typed,
  canonicalizing context store. No claim covers side channels, free-text
  bypasses, direct filesystem access or arbitrary caller-supplied context.
- Each `confirm` carries a principal identity supplied by the event and
  checked against `Roles.users`. The model does **not** prove that a real
  syscall or cryptographic protocol authenticates that issuer, or that
  approvals are semantically informed.
- Distinct context handles depend on the append-only trusted store; a runtime
  that reuses handles, discards provenance or remaps IDs needs its own proof.
- Effects cannot bypass the trusted mediator by premise. This does not prove
  network, filesystem, payments or all system-call effects are actually
  mediated; atomicity and external receiver idempotence remain separate roots.
- No runtime-to-model simulation, executable byte correspondence, crash
  semantics, or independently witnessed deployment test is claimed.

## Verification and follow-through

1. Run `lake exe cache get` and
   `lake build ControlStack.Scenarios.SC06OneUse`; check printed axioms.
2. Compare the elaborated `scoped_safe` against the exact English claim.
3. Develop a separate, versioned runtime v2 with opaque, non-reusable context
   capabilities and an independently authenticated user approver.
4. Exercise equal-valued cross-provenance values, replay, crash/restart, direct
   effect bypass, identity spoofing, concurrency, and alternate store paths.
5. Add a **runtime-event → Lean-step forward simulation** and hold-out tests,
   rather than equating a successful `by decide` toy example with runtime
   fidelity.
6. After the proof and correspondence are reviewed, update manifest/TrustRoot
   and generated ledgers without changing historical evidence.

The existing SC-06 scenario remains **CONDITIONAL**. A kernel-checked
alternate formal model would not establish deployment assurance.
