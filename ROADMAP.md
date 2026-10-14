# ROADMAP: control-stack, research refocus (revision 2, 2026-10-13)

Canonical status. Base commit of this revision: `main` at `e7b4b25`. Revision 1 (same day, merged as #64) set the
gated milestones; this revision corrects the Milestone 1 design after three model reviews, records Milestone 1 as
implemented, and re-plans Milestones 2 to 4 from what Milestone 1 showed. The chronological journal before the
refocus is archived unchanged in [docs/ROADMAP-HISTORY.md](docs/ROADMAP-HISTORY.md). Everything in this repository is
**model-written and model-reviewed; no independent human review has happened** (G1 below).

## Status at a glance

| Milestone | Status | Gate still open |
|---|---|---|
| M1 flagship: a hard audit budget against an adaptive attacker | **implemented; verified locally and by CI on the pull request** (commit and runs in [HANDOFF.md](HANDOFF.md)) | external human review (the packet is section 8 of the record); five stated gaps (M1 "not met") |
| M2 third protocol: defer-to-trusted in the same round model, where usefulness first differs | planned | reuse without silently strengthening assumptions |
| M3 discovery and accessibility | planned; the M1 record is the first card | a reader outside the project finds, instantiates and challenges one result; untested |
| M4 theory or experimental extension | planned; three ranked candidates in section 5 | answers a concrete question with an explicit evidence story |
| Deployment verifier track | **separated**, scoped R2, frozen except review-gated PRs | G1 human review, then G9 publish (owner) |

Owner decisions that this plan assumes but that have not been confirmed are in section 7.

## 1. Mission and scope

Build a reusable, machine-checked library for reasoning about AI control protocols, starting with monitoring,
auditing and adaptive attacks. A researcher should be able to take one checked result, see what it guarantees and
under which assumptions, see where it breaks, and know what evidence would be needed to apply it. Simulations and
reference implementations connect the mathematics to experiments; they do not validate a threat model.

Out of scope: verification of arbitrary Linux, Docker, Kubernetes, GPU or datacenter deployments. The existing
deployment verifier is preserved as a scoped application (section 6); its assurance claims are not expanded here.
"Mathlib for AI control" is a long-term aspiration, not a completion criterion for anything below.

**Kinds of knowledge.** Every major claim in a record is labelled twice. Kind: mathematical result (proved under
explicit assumptions), empirical finding (one experiment, dataset and procedure), modelling choice, or informal
argument or conjecture. Provenance: established; new formalisation of known mathematics; composition of existing
results with novelty unassessed; potential contribution needing a literature review; open conjecture. A proof added
here is not evidence of novelty. A value computed by an executable model is a model finding, not an empirical one. A
source is cited for a claim only after it has been read, with version and section.

## 2. Repository assessment

Grounded in a direct reading of the declarations named here, the flexibility test of 2026-10-13
([docs/FLEXIBILITY-TEST.md](docs/FLEXIBILITY-TEST.md)) and the M1 implementation.

**1. Reusable definitions and results** (all compile, standard axioms, no `sorry`).

- Round-kernel semantics, `ControlStack/Core/Leakage.lean`: `val`, `cval`, `Dominated`, `val_le_cval`,
  `seq_transfer`, `mass_le_pow`, `cval_live`, `val_congr_on`, `AOut`, `attackSet`, `liveInd`, `blind_audit`,
  `audit_leak_bound`. This is the base M1 was built on, with no change to it.
- `ControlStack/AuditBudget.lean`: `random_subset_survival`, `survival_le_pow`, `observable_schedule_nogo` (fixed
  attack sets).
- `ControlStack/Families/F6/ReservedAudit.lean`: `reserved_leak_bound`, `reserved_adaptive`, `reserved_policy_bound`,
  `pU`, `sum_pU`, `flag_audits_le`, `reserved_total_le`, `observable_and_exhausted`.
- `ControlStack/Families/F6/ReservedRecall.lean`: `hypMiss`, `adaptive_recall_bound` (imperfect reserved recall,
  flags hidden), `recall_instance_bound`.
- New in M1, `ControlStack/Families/F6/FlagBudget.lean`: `val_le_potential`, `cval_le_potential`, `val_mono`,
  `val_add`, the flag-budget bookkeeping, `binTail`, `flag_pre_bound`, `flag_exhaust_bound`, `flag_total_bound`.
- New in M1, `ControlStack/Families/F6/SplitAudit.lean`: `splitK`, `split_hidden_bound`, `split_flag_bound`,
  `split_min_bound`, `split_product_pre`, `split_product_bound`, three kernel witnesses.
- `ControlStack/DeferMono.lean` (`catVE_toReal_le_catV`) on `DeferGame.lean` (VCVio), and `ledger/TMCERT.lean`,
  `ledger/TMGAC.lean` (certificate checker for stateful trusted monitoring; exact 13/50 against 11/32 separation of
  constant-rate and clocked attackers). Reusable as mathematics; in other models (item 3).
- Records tooling: `tools/build_registry.py`, `registry/annotations.json`, `tools/build_statement_catalog.py`,
  `tools/build_lean_english_overview.py`, and new `tools/check_records.py`.

**2. Substantive proof duplication.**

- `ReservedRecall.lean` defines `attNC`, `phi`, `fac`, `phi_live`, `recallSucc` for `AOut Unit` only. M1 needed the
  same event for `AOut Bool` and defined `FlagBudget.totSucc` separately. Generalising the recall file to an
  arbitrary leak type would remove this and unlock imperfect reserved recall with visible flags (backlog item 2).
- The proofs of `reserved_adaptive`, `adaptive_recall_bound` and `audit_adaptive_hidden` each repeat the same
  closing steps (certificate mass ≤ 1 by `mass_le_pow`, then `cval_smul`, `cval_live`). `split_hidden_bound` repeats
  the mass step a fourth time. One lemma "S-independent certificate of unit mass" would replace all four; not done
  in M1 so that existing files stay byte-identical.
- SC-26 and SC-90 re-derive the append-only-log kit and reprove trace induction instead of using `Spec.trace_safe`
  (flexibility test, items 5-8). Outside M1; input to any gate-side refactor.

**3. Models that differ and must not be conflated.**

| model | where | time | attacker observes | budget | outcome |
|---|---|---|---|---|---|
| fixed attack set | `AuditBudget` | `Fin N`, no play | nothing | hard B | attack set disjoint from schedule |
| round kernel, flags hidden | `Leakage`, `ReservedAudit`, `ReservedRecall` | N rounds | own bits and catch flags | hard Bh; Bf in the kernel's hidden part | ≥ k attacks, none in S, never caught |
| round kernel, flags visible | `FlagBudget`, `SplitAudit` (M1) | N rounds | own bits, flags, catches | hard Bh and hard first-come Bf | ≥ k attacks, never caught |
| VCVio operational game | `DeferGame`, `Refinement*` | `Hist X Z` | policy-defined | audit budget b in a recursion | `catV` recursion |
| ledger certificate model | `ledger/TMCERT`, `TMGAC` (separate Lake project) | finite horizon | null, coin count or round index | audit coins | risk recursion |
| deterministic gate | `Core/Gate`, 28 scenarios, SC-90 | list traces | n/a (any trace) | counters in state | invariant on every legal trace |

No declaration connects the gate model, the VCVio game or the ledger model to the round kernel.

**4. Advertised conclusions that exceed the formal statements.**

- Revision 1 of this roadmap described M1 as a comparison of two protocols "both in `ReservedAudit.lean`".
  `reserved_policy_bound` quantifies over every flag law, so it credits the monitor with nothing; the second
  protocol had no theorem. Corrected by M1.
- Docstrings in `ReservedAudit.lean` call `observable_reserved_nogo` and `recall_zero_vacuous` "necessity"
  witnesses. Each shows that a bound fails on an instance when one premise is dropped; neither shows the premise is
  necessary in every formulation. The files are unchanged; the record uses the weaker wording.
- `AuditBudget` argues adaptivity in a prose remark; the adaptive statements are `Leakage.audit_adaptive_hidden` and
  the F6 ones.
- All round-kernel results bound "≥ k attacks and never caught by round N". "k attacks released before the first
  catch" is the event a designer cares about; the step between them is argued and numerically checked, not proved
  (note at `Leakage.survInd`; M1 "not met", item 1).
- SC-90's `harmful_effect_is_a_miss` is "every effect is Cleared"; the `harm` bit is never read.
- The deployment verifier's verdicts never exceed CONDITIONAL and rest on unproved faithful extraction and protocol
  refinement (`docs/DEPLOYMENT-CLAIM-v0.md`).

**5. Best starting point for the first demonstration.** `Leakage.seq_transfer` plus `ReservedAudit.reserved_leak_bound`:
the transfer form already admits a visible leak, which is what lets flags be shown to the attacker and the hidden
schedule bound survive. That is what M1 used.

**Responsibility areas** (boundaries, not a migration).

| area | directories |
|---|---|
| formal models and results | `ControlStack/Core/`, `ControlStack/Families/`, `ControlStack/AuditBudget.lean`, `ledger/` |
| research records | `docs/records/`, `registry/`, `THEOREM-REGISTRY.*`, `docs/lean-english/` |
| theory development | section 5 of this file, `theory/OPEN-OBLIGATIONS.md`, `ledger/questions/` |
| applications | `numerics/` (executable models), `deployment/`, `trusted_stack/`, `gateway/`, `scenarios/` |

## 3. How revision 2 was reviewed

Three model reviewers read the plan before any Lean was written: one for mathematical soundness, one for research
relevance, one hostile referee from a different model family. None is an independent human reviewer. What changed:

| objection | raised by | outcome |
|---|---|---|
| The flag theorem as first proposed bounded only attacks made before exhaustion, an event the attacker can avoid; that is a metric substitution | all three | the headline statement is about all attacks and carries an explicit exhaustion term (`flag_total_bound`) |
| The product of the two bounds is provable now, not a conjecture | soundness, referee | proved (`split_product_pre`, `split_product_bound`) |
| "The split gets the minimum of the two bounds" is false for the total-attack event | soundness (by its own computation) | the minimum is stated with the exhaustion term; the counterexample is a test |
| The dependence witness was misstated, and its first replacement refuted only a product with schedule-averaged recall | soundness, referee (twice) | replaced by a monitor with recall 1/2 for every schedule whose false positive leaks the schedule (`dependence_witness`) |
| Eight places where the record or a docstring claimed more than the Lean statement (statement audit of the finished work by the referee; no defect found in the statements themselves) | referee | all reworded; listed in HANDOFF.md |
| "P1 holds for any flags" is false once flags are visible | soundness, referee | the theorem requires the flag law to be a function of the visible history; stated as a limit |
| The recall premise contains most of the conclusion | referee | recorded in the assumption audit with the reason the theorem is still useful |
| Lead with the per-step ratio and the exhaustion probability; add the constant-rate attacker | relevance | done in the record and the executable model |
| "Released and never caught" excludes harm before a later catch | referee | recorded as not met (item 1 below); first step of M2 |
| Cut the reduced-state optimal-attacker programme | relevance | kept, but validated against exhaustive recursion in the tests |

## 4. Milestones

### Milestone 1: the flagship demonstration (implemented)

**Question.** What can a hard audit budget guarantee against an attacker who adapts to what it observes, when audits
are spent on a hidden random schedule (P1), on monitor flags first come first served (P2), or split, and which
guarantee fails when the schedule leaks, the flag budget is exhausted, or recall holds only on average?

**Record.** [docs/records/budgeted-audit-vs-adaptive-attacker.md](docs/records/budgeted-audit-vs-adaptive-attacker.md)
holds the answer, model, event order, exact declarations, negative controls, executable example, assumption audit,
provenance and the review packet. It is the single place to read; this section only tracks acceptance.

**What a useful answer was defined to be.** A bound per protocol that is uniform over the attacker class, with the
premises each one needs and does not need, plus a witness for each failure. A negative answer counts: a protocol
with no informative bound in a regime, or two bounds that do not compose, stated with the obstruction.

| acceptance item | output | status |
|---|---|---|
| A. two related protocols, compatible semantics | `SplitAudit.splitK` (P1 is Bf = 0, P2 is Bh = 0); the two mechanisms differ in kind (information hiding against conditional detection), not only in parameters | checked |
| B. a useful bound with explicit assumptions | `split_hidden_bound`, `flag_total_bound`, `split_flag_bound`; informative regimes and the k = 1 limitation (`hidden_one_step`) in the record | checked |
| C. reuse or composition | `split_product_bound` = existing `seq_transfer` + new `pre_step`; reuse and obstruction list in the record, section 3 | checked |
| D. negative control | `exhaustion_witness`, `average_recall_witness`, `dependence_witness` (new, Lean), `observable_schedule_nogo` (existing) | checked |
| E. connection to experiments | `numerics/budgeted_audit.py`, 12 checks, frozen results; measurement table in the record, section 5 | checked (executable-model agreement only) |
| F. result record | the record, with `tools/check_records.py` validating references | checked |
| review packet for an outside reader | record, section 8 | written; **no reviewer asked** |

**Not met in M1** (positive objectives that remain open; none is hidden in an assumed lemma).

1. The safety event is "≥ k attacks and never caught by round N". That "k attacks released before the first catch"
   has the same supremum is argued and confirmed by exhaustive computation for N ≤ 5, not Lean-checked.
2. Reserved audits are perfect in the visible-flag model. Imperfect reserved recall is proved only with hidden flags.
3. Honest-task usefulness does not distinguish the protocols (none of them blocks or defers); only audits spent do.
4. The exhaustion premise bounds "flag and not caught", which includes false positives the attacker induces. No
   statement separates honest false positives from induced ones.
5. Two of four cited papers were read only as abstracts; the other two through an automated fetch of their HTML.

**Excluded on purpose:** trusted editing, resampling, suspicion scores and thresholds that vary with time or budget,
side channels outside the visible history, the gate bridge, any ControlArena or inspect_ai adapter.

### Milestone 2: a third protocol in the same foundations (planned)

**Defer-to-trusted at a flag, in the round kernel.** A flagged round with no audit budget left (or below an audit
threshold) is replaced by the trusted model's action instead of being released. This is the first protocol in which
honest usefulness differs, so it forces a usefulness quantity: the expected number of honest rounds not deferred.

Steps, in order:

1. **Truncation lemma** (closes M1 item 1): for kernels in which a non-attack round is never caught, the supremum of
   "k attacks released before the first catch" equals that of "≥ k attacks, never caught". Needed before any
   statement about harm.
2. **The defer kernel and its two quantities**: safety by `val_le_potential` with a potential in which a deferred
   attack is neither released nor caught; usefulness as an exact expectation over honest play.
3. **Evaluation of reuse**: which of `flagCount`, `preAtt`, `pre_step`, `tail_step`, `splitK` carried over unchanged,
   which needed a new case, and whether exhaustion still costs safety (expected: it now costs usefulness instead).
4. **Relation to `DeferMono.lean`** (VCVio): either a statement that both models give the same number on a
   shared instance, or an obstruction record. No bridge lemma that assumes the correspondence.

- Dependencies: M1 modules; `DeferGame.lean` for step 4.
- Outputs: one Lean module, its record, an extension of `numerics/budgeted_audit.py`, a refactor only where two
  protocols needed the same thing (candidates in section 2, item 2).
- Risks: the usefulness quantity may be trivial unless the monitor's honest flag rate is in the model as a
  distribution over tasks rather than a constant; step 1 may need a coupling that the `val` semantics makes awkward.
- Acceptance: reuse works without strengthening assumptions or erasing protocol differences, and the record says
  which M1 statements were used verbatim.
- Status: planned.

### Milestone 3: discovery and accessibility (planned)

Execute the relevant part of `docs/PLAN-RESEARCHER-FRIENDLY.md`: the M1 record is the first claim card; add a
protocol-to-declarations index for the round-kernel family; one tutorial that instantiates `flag_total_bound` and
`split_product_bound` at a reader's own (N, Bh, Bf, k, ρ, α) with `numerics/budgeted_audit.py`; a pattern page for
the round kernel. Then name the next limited set of formalisations.

- Dependencies: M1 record format and `tools/check_records.py`; M2 for a second record.
- Outputs: the index, the tutorial, the pattern page, records for the existing F6 results that M1 reused.
- Risks: usability cannot be assessed by the authors. Acceptance needs a reader outside the project.
- Acceptance: a reader finds a relevant result, identifies its assumptions and instantiates it without reading
  unrelated modules. Record whether that has been tested; until a person has done it, it is untested.
- Status: planned.

### Milestone 4: theory or experimental extension (planned)

Chosen from section 5 after M2 reports what was hard. Each candidate carries a counterexample to look for first.
The gate-to-probability bridge (revision 1's M2 step 2) moves here as a candidate, not a commitment: SC-90 and the
round kernel index time differently (request ids against rounds) and SC-90's `harm` bit is unread, so the first
output would be an obstruction record.

- Dependencies: M1, M2.
- Outputs: one extension with its record; or a verified obstruction.
- Risks: new mathematics is desirable, not guaranteed.
- Acceptance: the extension answers a concrete question and has an explicit verification and evidence story.
- Status: planned.

## 5. Research backlog (three, ranked)

1. **Paced flag budgets against time-aware attackers.**
   - Question: can a threshold that depends on rounds and audits remaining remove the exhaustion term, or does it
     only move the weakness to the rounds where the threshold is high?
   - Candidate result: for a rule that reserves part of the flag budget for the last rounds (or a per-window quota),
     a bound (1−ρ_min)^k + a strictly smaller tail; and a matching lower bound for every stationary first-come rule
     with αN ≥ Bf.
   - Assumptions: recall as a function of the threshold (an ROC curve) is given per history, not on average.
   - Existing dependencies: `flag_total_bound` already holds for any history-dependent flag law with ρ the minimum
     recall and α the maximum flag rate; `ledger/TMGAC.lean` has the three-round separation.
   - Possible counterexample: pacing lowers recall late in the run, which is exactly the pattern of
     `average_recall_witness`; the attacker waits for the strict-threshold rounds.
   - Relevance: the literature's trusted-monitoring protocols set a threshold at the audit rate; M1's model says that
     calibration leaves an exhaustion probability near one half against an attacker who attacks late.
   - Novelty: potential contribution requiring literature review. Griffin et al. (2409.07985v2, section 4.1)
     optimise such thresholds against a memoryless Red; whether a time-aware Red is treated was not checked.
2. **Leakage-aware auditing, with imperfect reserved recall.**
   - Question: how fast does the hidden-schedule bound degrade as the attacker learns about S, and does the product
     with the flag bound survive imperfect reserved audits?
   - Candidate result: a quantitative degradation in the certificate mass of the leak (`audit_leak_bound` gives the
     form for perfect recall); a version of `split_product_bound` with `hypMiss` in place of the hypergeometric
     ratio.
   - Assumptions: the leak channel is the only extra observation; S uniform a priori; recall coins independent of
     the attacker given the history.
   - Existing dependencies: `Leakage.audit_leak_bound`, `ReservedRecall.adaptive_recall_bound`; needs the recall
     lemmas generalised from `AOut Unit` (section 2, item 2).
   - Possible counterexample: a one-bit leak that says whether round 1 is reserved may already let a k-step attack
     gain more than a factor of 2; shared detection failures between the reserved auditor and the monitor break the
     product.
   - Relevance: real audit queues leak through timing and reviewer behaviour.
   - Novelty: composition of existing results; unassessed.
3. **Cumulative damage instead of a first catch.**
   - Question: if catching does not end the run and each released attack step does bounded damage, what is the
     expected cumulative harm under P1, P2 and the split?
   - Candidate result: an expected-damage bound per protocol and a damage-against-audits frontier.
   - Assumptions: bounded per-step damage; catches remove only the caught step.
   - Existing dependencies: `Families/F6/DamageBound.damage_bound`; `val_add` and `val_mono` from M1.
   - Possible counterexample: an attacker who front-loads damage makes the per-step bound tight and the frontier
     trivial.
   - Relevance: the setting where no single action is catastrophic (Wen et al., 2411.17693v1, abstract only read).
   - Novelty: new formalisation unless it goes beyond the frontiers in 2409.07985.

Retired from the active list in this revision: dependence-sensitive composition of trusted and untrusted monitoring
(the collusion stack is deferred; the dependence question for audits was answered in M1 by `split_product_bound` and
`dependence_witness`). To add an item, retire one.

## 6. Classification of existing work

| Work | Classification | Where | Note |
|---|---|---|---|
| F6 audit-budget theory | **continued**; reuse base of M1 | `AuditBudget.lean`, `Families/F6/` | Existing files unchanged by M1. |
| Round-kernel and leakage core | **continued** | `Core/Leakage.lean` | Unchanged. |
| Stateful trusted-monitoring certificates (TMCERT, TMGAC) | **continued as a reference point** | `ledger/`, `fidelity/TMGACF1.md` | Different model; cited by M1 for the clocked-attacker separation; re-enters with backlog item 1. |
| Defer game (VCVio) | **continued into M2 step 4** | `DeferGame.lean`, `DeferMono.lean` | Compare, do not bridge by assumption. |
| Flexibility test and SC-90 | **deferred to M4** | `docs/FLEXIBILITY-TEST.md`, `docs/flexibility-test/` | SC-90 stays outside the Lake build. |
| Layer-1 collusion stack (UMPROT, honeypots, mediator, canonicaliser) | **deferred** | `STACK.md`, `Refinement*.lean`, `Families/F6/MonitorCollusion.lean` | Verified; no active milestone uses it. |
| Empirical certificates (PREREG-*, `Core/Cert`) | **deferred** | `PREREG-*.md`, `assurance/` | The route from estimates to checked certificates; M1's bounds with measured inputs are illustrative until it is used. |
| 28 scenario bundles and the generator | **deferred** | `scenarios/`, `tools/new_scenario.py` | Deterministic enforcement; kept separate from the quantitative models. |
| Researcher-friendly plan | **continued into M3** | `docs/PLAN-RESEARCHER-FRIENDLY.md` | Unchanged design. |
| Deployment verifier (Tiers 1-12, scoped R2) | **separated** | `END-STATE.md`, `deployment/`, `docs/DEPLOYMENT-CLAIM-v0.md` | Frozen at CONDITIONAL; owner- or hardware-gated (G1, G4, G6, G9). Claims not expanded. |
| PR #56 (`audit/lean-reuse-187-20261011`) | **continued, review-gated** | GitHub | Do not merge without independent human review. |
| Pause branch `audit/r2-v8-trusted-code-20261013` | **continued, review-gated** | `HANDOFF-PAUSE-2026-10-13.md` on that branch | Do not stack research work on it. |
| G8 non-Linux backends | **discontinued** | `END-STATE.md` | Owner decision 2026-10-13. Evidence preserved. |
| Chronological roadmap journal | **archived** | `docs/ROADMAP-HISTORY.md` | Unchanged. |

## 7. Owner decisions assumed by this plan (unconfirmed)

1. M1's pair and metrics as implemented: hidden random audits against first-come flag audits and their split; event
   "≥ k attacks, never caught"; cost "audits spent".
2. M2 is defer-to-trusted in the round kernel, and the gate bridge moves from M2 to an M4 candidate. Revision 1 had
   the gate bridge as M2 step 2.
3. Backlog item 1 is paced budgets, ahead of leakage-aware auditing; trusted-untrusted composition is retired from
   the active three.
4. Existing F6 files stay byte-identical until M2 shows which refactor two protocols need.
5. PR #56 and the pause branch stay frozen until a person reviews them.

Standing gates that need the owner, unchanged: G1 independent human review (the M1 record's section 8 for the
research track; `deployment/REVIEW-PACKET-R2.md` for the deployment track); G9 tag, publish, outreach; English
corrections on the pause branch; a human-authored held-out set.

## 8. Verification rules for every milestone

- Lean: no `sorry`, no new axioms; `#print axioms` on every headline declaration; statements reviewed, not only
  accepted proofs. Local toolchain is `~/.elan` (Lean 4.34, built Mathlib).
- Records: `python3 tools/check_records.py` must pass; it checks references and lexical dependencies, not meaning.
- Executable models: exact arithmetic where feasible; results frozen and reproduced in CI; every table labelled as a
  model value. A model value is never cited as an empirical finding.
- CI: cached "green" markers skip the Lean kernel. For a real run delete the `green-*` caches for the ref,
  re-dispatch, and confirm the "Skipped, identical inputs already passed here" step shows `skipped`. A new workflow
  file cannot be dispatched until it is on `main` (it does run on its own pull request). GitHub Actions only.
- Report per milestone: exact commit verified, commands or workflows, failures, skipped checks, unresolved
  obligations. Green CI does not establish specification fidelity or usefulness.
- Negative controls are required. A failed proof search is not a counterexample; a counterexample to one
  formulation does not show a premise is necessary in all of them.
- Additional model review is not independent human review. Record external review as pending until a person has
  done it.

## Maintenance

Update the status table and the milestone status lines when an output is checked, started or dropped. Session
journals go in `HISTORY.md`, not here. Keep section 5 at three items.
