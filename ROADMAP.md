# ROADMAP: control-stack, research refocus (2026-10-13)

Canonical status. Base commit of this revision: `main` at `462c9c7`. The chronological journal that this file replaces is
archived unchanged in [docs/ROADMAP-HISTORY.md](docs/ROADMAP-HISTORY.md). Everything in this repository is
**model-written and model-reviewed; no independent human review has happened** (G1 below).

## Status at a glance

| Milestone | Status | Gate |
|---|---|---|
| M1 flagship demonstration: budgeted auditing against an adaptive attacker | **not started**; reuse base identified (section 2) | all six M1 outputs checked, no `sorry`, standard axioms only |
| M2 extension beyond the initial pair (defer-to-trusted, then the deterministic gate bridge) | planned | reuse without silently strengthening assumptions |
| M3 discovery and accessibility | planned; `docs/PLAN-RESEARCHER-FRIENDLY.md` is the design | a reader finds, instantiates and challenges one result without reverse-engineering |
| M4 theory or experimental extension | planned; three ranked candidates in section 4 | answers a concrete question with an explicit evidence story |
| Deployment verifier track | **separated**, scoped R2, frozen except review-gated PRs | G1 human review, then G9 publish (owner) |

Owner decisions that this plan assumes but that have not been confirmed are listed in section 6. Change them there,
not by silently redefining a milestone.

## 1. Mission and scope

Build a reusable, machine-checked library for reasoning about AI control protocols, starting with monitoring,
auditing and adaptive attacks. The product is useful formal reasoning with accessible explanations: a researcher
should be able to take one checked result, see exactly what it guarantees and under which assumptions, see where it
breaks, and know what evidence would be needed to apply it. Simulations and reference implementations connect the
mathematics to experiments; they do not validate the threat model.

Out of scope for this roadmap: verification of arbitrary Linux, Docker, Kubernetes, GPU or datacenter deployments.
The existing deployment verifier (`deployment/`, `trusted_stack/`, `extractors/`) is preserved as a scoped application
(section 5) and its assurance claims are not expanded here. "Mathlib for AI control" is a long-term aspiration, not a
completion criterion for anything below.

## 2. Repository assessment (what the milestones build on)

Grounded in the flexibility test of 2026-10-13 ([docs/FLEXIBILITY-TEST.md](docs/FLEXIBILITY-TEST.md), one agent
session, not a review) plus a direct reading of the declarations named here.

**Reusable now (all compile with standard axioms, no `sorry`):**

- `ControlStack/AuditBudget.lean`: `random_survival_le_pow` (a k-step attack survives a uniform B-of-N hidden audit
  schedule with probability C(N-k,B)/C(N,B) ≤ ((N-B)/N)^k), `observable_schedule_nogo` (an observable schedule is
  avoidable), `budget_example` (N=100, B=10, k=5, exact binomials).
- `ControlStack/Families/F6/ReservedAudit.lean`: `reserved_adaptive` (the same bound uniform over every attacker whose
  attack bit has law σ(visible history); the attacker sees its own actions and every catch flag; the kernel's hidden part,
  including false-positive flags and flag-triggered audits, is arbitrary); `reserved_policy_bound` (the concrete
  reserved-plus-first-come-flag policy); `flag_audits_le`, `reserved_total_le` (audits ≤ Bh + Bf for every flag
  pattern, a resource-cost statement); witnesses `observable_reserved_nogo`, `observable_and_exhausted` (N=4: known
  schedule plus flag budget exhausted by false positives leaves a 2-step attack unaudited), `recall_zero_vacuous`.
- `ControlStack/Families/F6/ReservedRecall.lean`: `adaptive_recall_bound` (imperfect recall r: P(≥ k attacks, never
  caught) ≤ `hypMiss N Bh k r`, uniform over the same adaptive class), `adaptive_recall_two_term`, `recall_instance_bound`.
- `ControlStack/DeferMono.lean`: `defer_mono` (lower bounds on audit recall, halt hazard and trusted-service catch rate
  give an upper bound on the operational catastrophe probability via the `catV` recursion), on top of
  `ControlStack/DeferGame.lean` (VCVio).
- `ControlStack/Core/Gate.lean` (`Gate.System`, `Gate.Spec`, `trace_safe`) and the deterministic scenario
  `docs/flexibility-test/SC90TrustedMonitorAudit.lean` (trusted monitoring with a finite audit budget as an admission
  rule: `sc90_safe`, `harmful_effect_is_a_miss`, `exhausted_blocks`, seven necessity witnesses). Kept outside the Lake
  build on purpose.
- Records tooling: `tools/build_registry.py` (declaration registry; adversary class for 75 of ~2237 declarations),
  `tools/build_lean_english_overview.py`, `docs/lean-english/` (plain-English statements, dependency extraction). The
  traceability builder and the one-to-one blind checks live on the pause branch `audit/r2-v8-trusted-code-20261013`.

**Duplication:** SC-26 and SC-90 re-derive the append-only-log kit (key uniqueness, append monotonicity, "injects into a
capped list") and reprove the trace induction and absorbing halt instead of using `Spec.trace_safe` and `withHalt`
(flexibility test, section 3, items 5-8). Not blocking for M1; input to M2 refactoring.

**Models that differ and must not be conflated:** the round model (`Fin N`, kernels `K S h z`, real-valued sums) used
by `AuditBudget`/F6; the VCVio operational games (`ProbComp`, `Hist X Z`) used by `DeferGame`/`Refinement`; the
deterministic list-trace gate (`Gate.System`) used by the 28 scenarios; and the `ledger/` project (`catV` linked by
textual copy, separate Lake project). No declaration connects the gate model to either probabilistic model.

**Advertised conclusions that exceed the formal statements:** SC-90's `harmful_effect_is_a_miss` is "every effect is
Cleared"; the `harm` bit is never read, so the sentence is a labelling. `AuditBudget` is stated for a fixed attack set
and adaptivity is argued in prose; the adaptive statements are the F6 ones. The deployment verifier's verdicts never
exceed CONDITIONAL and rest on unproved faithful extraction and protocol refinement (`docs/DEPLOYMENT-CLAIM-v0.md`).

**Best starting point for M1:** `ReservedAudit.lean` already contains both protocols of the flagship pair in one
semantics, and `ReservedRecall.lean` the imperfect-recall version. The flagship is therefore mostly composition,
examples, a negative control and a record, not new mathematics.

## 3. Milestones

### Milestone 1: the flagship demonstration (not started)

**Question.** What can a limited-budget auditing protocol guarantee against an attacker who adapts to what it can
observe, and which guarantees fail when the audit schedule leaks, the monitor's recall drops, or the flag budget is
exhausted by false positives?

**Decision it informs.** Whether to spend an audit budget on a hidden random schedule, on monitor-flag-triggered
audits, or on a split, when the attacker is adaptive and the monitor is imperfect.

**The two protocols** (both in `ReservedAudit.lean`, same round model):

- P1, hidden random auditing: a uniformly random reserved set S of Bh rounds, drawn before round 1 and never revealed.
- P2, monitor-assisted auditing: a first-come flag-triggered budget Bf; a flagged round is audited while fewer than Bf
  earlier rounds were flagged. False positives consume the budget.
- The concrete policy combines them (Bh reserved plus Bf flag-triggered, `reserved_policy_bound`), so the comparison
  is P1 against P2 and against the split.

**Event order per round i = 1..N.** Attacker chooses the attack bit a_i with law σ(visible history), where the visible
history is its own earlier bits and every earlier catch flag. The monitor emits a flag (arbitrary, may be adversarial).
The round is audited if i ∈ S, or if flagged and the flag budget is not exhausted. A reserved audit of an attack round
catches with probability at least r; catch is an absorbing halt. Otherwise the action is released.

**Budget model.** Hard caps Bh and Bf on counts of audited rounds (`reserved_total_le`), not an expectation.

**Safety objective.** P(at least k attack rounds are released and the attacker is never caught), uniformly over the
adaptive class above. The one-harmful-release event is the case k = 1.

**Cost quantity.** Audits spent, at most Bh + Bf for every flag pattern. This is a resource cost, not task
usefulness; usefulness is unmodelled in this repository (flexibility test, item 7) and M1 says so rather than
substituting a proxy.

**Outputs** (acceptance is all six, checked):

1. Two concrete models stated side by side with a shared parameter record (N, k, Bh, Bf, r) and the shared success
   event, reusing the existing declarations rather than restating them.
2. The bound: `reserved_adaptive` / `adaptive_recall_bound` applied to P1 and to the split policy, and the explicit
   statement that P2 alone has no attacker-independent bound (its guarantee is entirely the monitor's conditional
   recall against the adaptive attacker). Informative regime shown: the bound is near-vacuous at k = 1 (it is 1 − Bh/N)
   and informative when the attacker needs k ≳ (N/Bh)·ln(1/ε) released steps; a short table of (N, Bh, k) values.
3. Reuse record: what was reused by name and what remained protocol-specific (the flag bookkeeping lemmas).
4. Negative controls, Lean-checked: schedule leakage (`observable_schedule_nogo`), false-positive exhaustion
   (`observable_and_exhausted` generalised to a stated family if feasible), recall zero (`recall_zero_vacuous`), and one
   new witness that average monitor recall does not give the conditional recall the bound needs (a two-type attacker
   with the same average recall and a different bound).
5. Executable example: a Python exhaustive enumeration for small N (≤ 12) of the exact miss probability for P1, P2 and
   the split against a greedy adaptive attacker, compared with the closed form; plus the N = 100 instance. States
   what an experiment would measure (per-round recall on attack rounds at the deployed threshold, false-positive rate,
   leakage of S), which parameter each measurement informs (r, Bf consumption, the hidden-schedule premise), the
   assumptions needed to connect them (recall measured on the same attack distribution and history as the bound's
   conditional premise; a point estimate is not a worst-case r), and what the evidence cannot establish (the attacker's
   class, side channels outside the model).
6. Result record in the existing records format (`docs/lean-english/` pattern, registry entry via
   `tools/build_registry.py`): plain-English statement and exact declaration, assumptions with the seven-point
   assumption audit (role, why needed, kind, how to challenge, whether a measurement matches the quantifiers,
   plausibility, what changes when weakened), event order, provenance (hypergeometric survival: established;
   adaptive-attacker uniformity and false-positive exhaustion: new formalisation of known reasoning; novelty of the
   split-policy comparison: unassessed), dependencies, worked example, counterexample, decision informed,
   verification status, review needs.

**Dependencies.** `AuditBudget.lean`, `F6/ReservedAudit.lean`, `F6/ReservedRecall.lean`, `Core/Leakage.lean`,
`Witnesses/Necessity.lean`; local Lean toolchain (`~/.elan`, Lean 4.34, built Mathlib).

**Risks.** (a) The cost quantity is weaker than what a protocol designer wants; recorded, not hidden. (b) The
adaptive class excludes attackers who see the monitor's score or the audit queue; a leakage-aware class is M4
candidate 1. (c) The "average recall is not conditional recall" witness needs a small new model; if it does not fit the
round model, it is recorded as an informal argument, not a theorem. (d) Nothing in M1 bridges to the deterministic
gate; see M2.

**Explicitly excluded in M1:** task usefulness, trusted editing, resampling, suspicion-score thresholds, side channels
outside the visible history, the gate-to-probability bridge, any ControlArena or inspect_ai adapter.

### Milestone 2: extension beyond the initial pair (planned)

Two steps, in order.

1. **Defer-to-trusted as the third protocol.** Connect `defer_mono` (`DeferMono.lean`, VCVio game) to the M1 parameter
   record: same recall premise r, same absorbing catch, the defer branch only after budget exhaustion. Evaluate which M1
   definitions carry over (recall, budget, success event) and which do not (the VCVio history type versus `Fin N`
   rounds; `catV` is a recursion, not a closed form). Acceptance: either a compatible restatement with the
   connecting obligations listed, or an explicit obstruction record.
2. **The deterministic gate bridge.** The flexibility test's top-ranked gap: no declaration turns SC-90's "every
   harmful effect is a monitor miss or an audit miss" plus the M1 probability bound into
   P(harmful effect reaches the ledger) ≤ f(r, Bh, Bf, N). First output is the precise obstruction (round index versus
   request id; flag-triggered versus hidden budgets; state-independent `legal`), then the smallest bridge lemma that
   closes it, if one exists. A bridge that assumes the conclusion is not accepted.

Refactor on the evidence from both steps: the shared log kit and `trace_safe_legal` from the flexibility test, only
where two protocols actually needed them. Acceptance: reuse works without strengthening assumptions or erasing
protocol differences.

### Milestone 3: discovery and accessibility (planned)

Execute `docs/PLAN-RESEARCHER-FRIENDLY.md` in this order: the M1 record as the first claim card; a
protocol-to-declarations index (the flexibility test's table, section 2, as a maintained file); pattern pages for the
gate invariant, the round model and the VCVio game; one end-to-end tutorial that instantiates the M1 bound at a
reader's own parameters. Then name the next limited set of formalisations. Acceptance: a reader finds a relevant
result, identifies its assumptions and instantiates it without reading unrelated modules. Record whether this has
actually been tested with a reader; until then it is untested.

### Milestone 4: theory or experimental extension (planned)

Chosen from the backlog in section 4 after M1 and M2 report what was actually hard. New mathematics is desirable, not
guaranteed; each candidate carries an explicit counterexample to look for first.

## 4. Research backlog (three, ranked)

1. **Leakage-aware auditing.** Question: how fast does the hidden-schedule bound degrade as the attacker learns bits
   about S (timing, queue position, monitor score)? Candidate result: with at most ℓ bits of leakage about S the
   survival bound degrades by a factor ≤ 2^ℓ, using the maximal-leakage tools in `Core/Leakage.lean`. Assumptions: the
   leakage channel is the only extra observation; S still uniform a priori. Existing dependencies: `reserved_adaptive`,
   `Core/Leakage.lean`, `LeakWitness`. Possible counterexample: `observable_schedule_nogo` is the ℓ = log₂ C(N,Bh)
   endpoint; a one-bit leak that reveals whether round 1 is reserved may already let a k-step attack avoid more than a
   factor of 2. Relevance: real audit queues leak. Novelty: unassessed; maximal-leakage bounds are classical, the
   application to audit schedules may not be.
2. **Dependence-sensitive composition of trusted and untrusted monitoring.** Question: when can the trusted-monitoring
   audit bound and the untrusted-monitoring collusion bound (`ComposeGame.lean`, the τ factor) be multiplied?
   Candidate result: an explicit conditional-independence premise under which the product holds, and a two-monitor
   witness with shared blind spots (`F6/MonitorEnsemble.blind_spot_escape`) where it fails. Relevance: protocol
   stacks are routinely scored as if independent. Novelty: composition of existing results, unassessed.
3. **Damage before intervention with a usefulness cost.** Question: if catch is not absorbing and each released attack
   step does bounded damage (`F6/DamageBound.damage_bound`), what is the expected cumulative harm under P1 versus the
   split, and what is the cost in audits and deferrals? Candidate result: a closed-form expected-damage bound and a
   safety/cost frontier for the two policies. Assumptions: bounded per-step damage, defer only at exhaustion.
   Possible counterexample: an attacker who front-loads damage so that the per-step bound is tight makes the frontier
   trivial. Relevance: the first usefulness-flavoured quantity in the repository. Novelty: Games for AI Control
   (2409.07985) has safety/usefulness frontiers; this would be a new formalisation unless it goes beyond them.

## 5. Classification of existing work

| Work | Classification | Where | Note |
|---|---|---|---|
| Deployment verifier (Tiers 1-12, scoped R2) | **separated** | `END-STATE.md`, `deployment/HANDOFF-NEXT.md`, `deployment/REVIEW-PACKET-R2.md`, `docs/DEPLOYMENT-CLAIM-v0.md` | Frozen at CONDITIONAL. Remaining items are owner- or hardware-gated (G1, G4 cluster, G6, G9, host coverage). Assurance claims are not expanded by this roadmap. |
| PR #56 (`audit/lean-reuse-187-20261011`) | **continued, review-gated** | GitHub | Do not merge without independent human review. |
| Pause branch `audit/r2-v8-trusted-code-20261013` (90 commits past main, no PR) | **continued, review-gated** | `HANDOFF-PAUSE-2026-10-13.md` on that branch | Blind one-to-one checks, English corrections (none applied), Landlock, second host, attack arms. Do not stack M1 on it. |
| Flexibility test and SC-90 | **continued into M1/M2** | `docs/FLEXIBILITY-TEST.md`, `docs/flexibility-test/` (copied here from b317905) | SC-90 stays outside the Lake build until M2 step 2 decides its place. |
| F6 audit-budget theory | **continued into M1** | `AuditBudget.lean`, `Families/F6/` | The reuse base. |
| Layer-1 collusion stack (UMPROT, honeypots, mediator, canonicaliser; proofledger CIDs) | **deferred** | `STACK.md`, `Refinement*.lean`, `Families/F6/MonitorCollusion.lean` | Verified; re-enters via backlog item 2. |
| Empirical certificates (PREREG-*, `Core/Cert`) | **deferred** | `PREREG-*.md`, `assurance/` | The existing place where point estimates become Lean-checked certificates; M1 output 5 cites it for estimation uncertainty. |
| 28 scenario bundles and the generator | **deferred** | `scenarios/`, `tools/new_scenario.py` | Parameters, state fields and state-dependent `legal` wait for M2 evidence (flexibility test items 3, 5). |
| Researcher-friendly plan | **continued into M3** | `docs/PLAN-RESEARCHER-FRIENDLY.md` | Unchanged design. |
| G8 non-Linux backends | **discontinued** | `END-STATE.md` | Owner decision 2026-10-13. |
| Chronological roadmap journal (2026-10-07 to 10-11) | **archived** | `docs/ROADMAP-HISTORY.md` | Historical evidence, unchanged. |

## 6. Owner decisions assumed by this plan (unconfirmed)

1. The flagship pair and metrics in M1: hidden random auditing versus flag-triggered auditing (and their split),
   failure event "≥ k attacks released and never caught", cost "audits spent". If a different safety or usefulness
   quantity is wanted, say so before M1 starts; the plan does not substitute one later.
2. M1 work branches from `main`, not from the pause branch; the flexibility-test documents are carried over as docs.
3. The gate bridge is an obstruction record in M1 and a build attempt only in M2.
4. PR #56 and the pause branch stay frozen until a person reviews them.

Standing gates that need the owner, unchanged from before: G1 independent human review (start with
`deployment/REVIEW-PACKET-R2.md` for the deployment track; the M1 record for the research track); G9 tag, publish,
outreach; English corrections on the pause branch; a human-authored held-out set.

## 7. Verification rules for every milestone

- Lean: no `sorry`, no new axioms; `#print axioms` on every headline declaration; statements reviewed, not only
  accepted proofs. Local toolchain is `~/.elan` (Lean 4.34, built Mathlib); `test_cert_ledger`, `test_portfolio_ledger`,
  `test_trust_root` fail locally for want of `ControlStack.Core.Cert.olean` and pass in CI.
- CI: cached "green" markers skip the Lean kernel. For a real run delete the `green-*` caches for the ref, re-dispatch,
  and confirm the "Skipped, identical inputs already passed here" step itself shows `skipped`. A new workflow file cannot
  be dispatched until it is on `main`. GitHub Actions only; no substitute CI.
- Report per milestone: exact commit verified, commands or workflows, failures, skipped checks, unresolved
  obligations. Green CI does not establish specification fidelity or usefulness.
- Negative controls are required, not optional; a failed proof search is not a counterexample.
- Additional model review is not independent human review. Record external review as pending until a person has done it.

## Maintenance

Update the status table and the milestone status lines when a milestone output is checked, started or dropped. Do not
append session journals here; put them in `HISTORY.md`. Keep section 4 at three items: to add one, retire one.
