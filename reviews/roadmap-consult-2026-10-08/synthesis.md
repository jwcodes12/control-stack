# Astra and Opus xhigh consultation: roadmap disposition

Date: 2026-10-08. User explicitly requested both consultations. Astra used native
`gpt-6-astra` at xhigh and read repository sources. Opus used exact
`claude-opus-5-5 --effort xhigh` on a static source packet with tools disabled.
The response metadata confirms the served Opus model and successful completion.
Neither review ran tests or demonstrated a new exploit. Source packet hashes and
review provenance are stored alongside these reports. The full static source
packet and raw Opus response are retained in the local research checkout.

## Main correction

The prior proposed roadmap mixed the selected bounded exact-secret-recovery
scenario with monitor-based bad-action safety. The former uses the complete
lifetime receiver observation space and an exact cardinality bound. The latter
uses risk/usefulness certificates whose rows depend on monitoring rates and
coverage. They share assurance infrastructure but have different proof premises.

SC-03 egress CI is complete. It proves/tests immediate-peer confinement under its
stated assumptions. Allowed CONNECT tunnels and the secret-delivery controls
show why it does not supply confidentiality or bound what an allowed peer sees.
General process attribution remains useful for SC-03, but does not discharge
receiver-view completeness, host-deputy influence, or allowed-sink leakage.

## Agreement and disagreement

Both reviewers prioritize the selected scenario's precise contract, lifetime
observation/accounting, honest usefulness, and a reproducible conditional safety
case. Both reject promoting sampled average FNR to a universal content-adaptive
attack guarantee and distinguish generic formal theorems from engineering patterns.

Astra ranks integrated topology/receiver-view and lifetime contracts first, then
targeted correspondence and usefulness. Opus ranks a usefulness viability gate
first and recommends narrowing/time-boxing egress work for this scenario. Root's
disposition: specify the honest task, accepted usefulness floor, lifetime/horizon
and complete observation boundary first; run usefulness and lifetime/channel
falsification work in parallel. Egress integration is supporting work, or a
separate reachability milestone when no network is needed by the honest task.

Astra proposes EgressGate/AuditDispatch as the smallest formal gate-interface
reuse test. Opus proposes the existing structural and monitor scenarios as clients
of one evidence schema/verifier. Preserve both: start the common evidence format
early, then choose a small formal interface using existing clients. No auditgate
implementation change is authorized or made by this consultation. The optional
monitoring scenario is a proposed second client, not a newly selected deployment.

## Recommended next milestones

1. Complete the Scenario A contract: a real bounded-message multi-instance task,
   baseline, predeclared usefulness target, episode and lifetime horizon, trusted
   receiver lineage, and every receiver-visible output. Keep network disabled
   unless needed; then count permitted sinks as channels or justify their exclusion.
2. Test usefulness and enforce the lifetime contract: required certified-path
   ledger, trusted lineage identity, serialized/transactional admission, durable
   restart semantics, and missing/corrupt/rollback-state behavior. In parallel,
   attempt the listed shared-kernel/page-cache and other residual channels.
3. Establish targeted gateway correspondence: accepted payloads, reachable views,
   blanking, delivery schedule, exact cardinality and lifetime charges. A small
   executable Lean decision core is an option; a full Python-plus-Linux proof is
   not the immediate milestone. Keep all unproved correspondence assumptions explicit.
4. Produce a walking safety case: one command checks the exact theorem/config,
   runtime controls, measured actual task success, receipt hashes and every
   unresolved premise. Bind cited CI and proof checks to exact revisions.
5. Demonstrate reuse: structural Scenario A and an optional monitor Scenario B
   use a common evidence/obligation format. Factor only small proven interfaces
   with concrete second clients. Measure rates for B only after specifying its
   actual protocol, content-coverage restriction and honest workload.

Full egress integration can proceed as its bounded separate track with direct
peer/failed-connect/missing-trace/inherited-FD/alternate-send controls. Namespace
attribution by construction is Opus's alternative to expanding syscall correlation;
compare engineering cost against the simpler outer-loopback calibration before
choosing. Neither topology discharges host deputies' causal influence by itself.

## Reusable assets and their limits

- Covert finite-view/schema/lifetime bounds: generic model results; require complete
  observation, exact cardinality, correct lifetime scope, and the stated secret
  distribution/independence. They do not prevent a one-bit harmful command.
- TMCERT risk and usefulness checkers: generic finite-game results; require lawful
  covered rows, actual protocol semantics, and a reward tied to real task success.
- TMLIP transfer: risk-only parameter/row-distance transfer with explicit inflation;
  it does not establish coverage or transfer usefulness automatically.
- Composition results: reusable under their specific common-game, conditional
  independence or restricted-population premises. No multiplication of marginal
  error rates without the appropriate joint guarantee.
- EgressGate/AuditDispatch: scenario model proofs and candidates for a shared gate
  skeleton; a generic runtime refinement library is not implemented.
- Mutated independent oracles, positive controls, capture-loss gates, source hashes
  and premise/evidence manifests: reusable engineering patterns, not universal
  observation-completeness proofs.

## Root checks and qualifications

Root inspected `gateway/gateway.py` and `gateway/harness.py`: `LifetimeLedger.charge`
is an unlocked read-modify-write followed by atomic replacement, missing state
starts fresh usage, and ledger is optional. These are real code-level correspondence
obligations for concurrent/persistent invocation. No race, rollback or side-channel
exploit was executed; the current sequential fixture is not thereby shown broken.

Opus's categorical statement that the observation premise is already false is
stronger than the supplied evidence: shared kernel state is an acknowledged
unresolved channel, not a demonstrated exact-recovery exploit. Testing can falsify
a boundary; absence of a detectable channel at finite statistical power cannot
prove zero capacity. A fresh VM is an isolation mechanism, not automatic proof
that all microarchitectural channels vanish. Observed success above a small
probability bound must be assessed with a predeclared statistical test rather
than treating every empirical excess as a logical contradiction.

Opus also flags a reward-meaning issue in the numerical fixture. Review the
actual reward model before calling non-deferred rounds completed tasks. This
review does not invalidate the certificate theorem; it challenges correspondence
of its input reward to the intended usefulness claim.

## Verification and next step

No product code, theorem, assumption status or auditgate source changed. No new
runtime/Lean test was needed for this documentation consultation. Existing green
egress/fast CI receipts remain those recorded in the publication handoff. Review
artifacts and planning notes are checked with `git diff --check`.

Immediate next work is the Scenario A contract and usefulness viability experiment,
with lifetime accounting and residual-channel tests in parallel. Implementation of
these recommendations has not started in this consultation.
