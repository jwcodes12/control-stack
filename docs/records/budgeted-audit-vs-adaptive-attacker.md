# Record: what a hard audit budget guarantees against an adaptive attacker

Milestone 1 flagship of [ROADMAP.md](../../ROADMAP.md). Written 2026-10-13 on branch `research/m1-flagship-20261013`
(base `main` at `e7b4b25`). **Model-written and model-reviewed. No independent human review.** Sections marked
*interpretation* are manually authored prose; the checker validates declaration references, not English meaning.

## 1. The question and the answer

**Question.** A protocol may audit at most B of N rounds. It can spend audits on a hidden random schedule (P1), on
rounds a monitor flags, first come first served (P2), or split them. What does each choice guarantee against an
attacker who adapts to everything it has seen, and what breaks each guarantee?

**Answer** (each line is a Lean theorem or a Lean-checked counterexample; section 3 has the exact statements).

| | guarantee: P(at least k attacks, never caught) ≤ | needs | does not need |
|---|---|---|---|
| P1, Bh hidden audits | C(N−k,Bh)/C(N,Bh) ≤ (1 − Bh/N)^k | schedule hidden; flags carry no information about it | anything about the monitor |
| P2, Bf flag audits | (1−ρ)^k + P(Binomial(N, α) ≥ Bf) | recall ≥ ρ and false-positive rate ≤ α **at every history** while budget remains | secrecy: holds for a schedule and budget state the attacker knows |
| split, flags independent of the schedule | C(N−k,Bh)/C(N,Bh) · (1−ρ)^k + P(Binomial(N, α) ≥ Bf) | both sets of premises | |

| what goes wrong | P1 | P2 | witness |
|---|---|---|---|
| schedule leaks | bound fails (attacker avoids S) | unaffected | `AuditBudget.observable_schedule_nogo` |
| false positives exhaust the flag budget | unaffected if flags are a function of the visible history | an attacker who attacks late succeeds whenever earlier false positives used the budget, even at monitor recall 1 (probability α in the witness) | `SplitAudit.exhaustion_witness` |
| recall holds only on average | unaffected (monitor not used) | attacker picks the histories where recall is low | `SplitAudit.average_recall_witness` |
| flags depend on the schedule | not covered by the theorem; the flags can leak S | per-schedule bound still holds | `SplitAudit.dependence_witness` (product fails) |

Each "unaffected" cell is one failure at a time. A known schedule together with an exhausted flag budget leaves
attacks unaudited by both parts (`ReservedAudit.observable_and_exhausted`).

**The three numbers a designer should take away** (*interpretation*; model values from section 5):

1. **Per-step protection ratio.** Per released attack step, P1 removes a factor about 1 − Bh/N and P2 a factor
   1 − ρ. At a 2% budget and ρ = 0.5 that is 0.98 against 0.5. For a single-step catastrophe (k = 1) P1's bound is
   exactly 1 − Bh/N (`SplitAudit.hidden_one_step`): hidden random auditing alone guarantees almost nothing there, and
   becomes informative only for attacks needing k ≳ (N/Bh)·ln(1/ε) released steps (N = 1000, Bh = 20: ε = 0.1 needs
   k ≈ 115).
2. **Exhaustion probability.** P2's guarantee carries an additive term P(Binomial(N, α) ≥ Bf). If the flag threshold
   is calibrated so that expected false positives equal the budget (αN = Bf), that term is about 0.53 at N = 1000,
   Bf = 20. With the budget at twice the false-positive load (αN = Bf/2) it is 0.003.
3. **Conditional, not average, recall.** ρ must be a lower bound on recall at every history the attacker can reach
   while budget remains: the minimum over attack types and history classes at the deployed threshold, not the mean.

**Decision this informs.** How to split a hard audit budget, and how much headroom to leave above the false-positive
load. In the model, with a monitor that satisfies the conditional premises, flag-triggered audits dominate per step
and the hidden slice is insurance: it is the only part of the guarantee that survives a monitor whose conditional
recall is lower than measured. Whether that insurance is worth its audits depends on k and on how much the recall
premise is trusted; the theorems give both sides of that trade, they do not choose.

**A negative answer this record also gives.** A red team restricted to memoryless (constant-rate) attacks understates
risk when the flag budget is near the false-positive load. In the executable model at N = 1000, Bf = 20, α = 0.02,
ρ = 0.95, k = 1, the best constant-rate attacker succeeds with probability 0.073 and an attacker who simply attacks
in the last round, looking at nothing, with 0.552. With αN = Bf/2 the gap disappears (0.050 against 0.053). The same
sensitivity was already recorded for a three-round instance of a different model (`ledger/TMGAC.lean`, 13/50
against 11/32, `fidelity/TMGACF1.md`).

## 2. Model, event order, attacker

One round kernel, `SplitAudit.splitK`, in the `val` semantics of `ControlStack/Core/Leakage.lean` (finite sums over
real-valued kernels; no measure theory).

- **Before play.** A set S of Bh rounds is drawn uniformly from the Bh-subsets of the N rounds and kept hidden.
- **Round i = 0..N−1, in this order.**
  1. The attacker chooses the attack bit a with law σ(visible history). The visible history is every earlier round's
     (attack bit, flag, caught): its own actions, every monitor flag (hence the flag-budget state) and every catch.
  2. The monitor emits a flag f with law τ(S, visible history, a). For the hidden-schedule and product theorems τ
     must not depend on S.
  3. The round is caught iff a ∧ (i ∈ S ∨ (f ∧ fewer than Bf earlier rounds were flagged)). An audited attack is
     caught with certainty. A caught round ends the attacker's chance (every event below requires "never caught").
  4. Otherwise the action is released.
- **Budget.** Hard caps: Bh reserved audits and at most Bf flag-triggered audits, for every flag pattern
  (`ReservedAudit.reserved_total_le`, `ReservedAudit.flag_audits_le`). Not an expectation and not a rate.
- **Safety event.** `FlagBudget.totSucc k`: at least k attack rounds and no catch by round N.
- **Cost.** Audits spent, at most Bh + Bf. Honest-task usefulness is the same for P1, P2 and the split by
  construction, because none of them blocks, edits or defers an uncaught action (*modelling choice*). The first
  protocol in which usefulness differs is defer-to-trusted (Milestone 2).
- **Attacker class.** On `splitK`: any σ that is a function of the visible history; the monitor's coin in the
  current round is drawn after the attack bit. The general theorems (`FlagBudget.flag_total_bound` and its two
  parts) are weaker in structure and stronger in scope: they constrain an arbitrary sub-probability kernel only
  through `hrec` and `hfp`, impose no catch rule and no separate monitor coin, and so cover any attacker, monitor
  and audit behaviour for which those two inequalities hold. Quantifier order: (ρ, α) are fixed first, then the bound
  holds for every kernel satisfying the premises.
- **Histories.** The Lean premises quantify over every history (and, on `splitK`, every schedule), reachable or not.
  That is stronger than "every reachable history"; a measurement programme only needs the reachable ones, but no
  theorem here is stated with that weaker premise.

**Which kind of guarantee each statement is** (direction §5B):

| statement | kind |
|---|---|
| all bounds in section 3 | uniform over the adversary class above |
| premises `hrec`, `hfp` (ρ, α) | conditional at every history with budget remaining (all histories in the Lean statement) |
| `average_recall_witness`, first conjunct | performance against one specified attack distribution |
| any benchmark recall number | average over a fixed dataset; not a premise of any theorem here |

## 3. Statements and exact declarations

All in `ControlStack/Families/F6/`. `#print axioms` for each: `propext`, `Classical.choice`, `Quot.sound` only.

| plain English | Lean declaration |
|---|---|
| P1: for every attacker and every S-independent flag law, P(≥ k attacks, never caught) ≤ C(N−k,Bh)/C(N,Bh) | `SplitAudit.split_hidden_bound` |
| P2, any kernel: if, while budget remains, P(attack and not caught) ≤ (1−ρ)·P(attack) at every history, then P(≥ k attacks, ≥ k of them while budget remained, never caught) ≤ (1−ρ)^k | `FlagBudget.flag_pre_bound` |
| P2, any kernel: if, while budget remains, P(flag and not caught) ≤ α at every history, then P(budget exhausted, never caught) ≤ P(Binomial(N, α) ≥ Bf) | `FlagBudget.flag_exhaust_bound` |
| P2, any kernel, all attacks: P(≥ k attacks, never caught) ≤ (1−ρ)^k + P(Binomial(N, α) ≥ Bf) | `FlagBudget.flag_total_bound` |
| P2 on the split kernel, for every fixed schedule S (so also a known one) and S-dependent flags | `SplitAudit.split_flag_bound`, `SplitAudit.split_flag_bound_avg` |
| split: the minimum of the P1 and P2 bounds | `SplitAudit.split_min_bound` |
| split, S-independent flags: the pre-exhaustion event has probability ≤ C(N−k,Bh)/C(N,Bh)·(1−ρ)^k | `SplitAudit.split_product_pre` |
| split, S-independent flags, all attacks: ≤ C(N−k,Bh)/C(N,Bh)·(1−ρ)^k + P(Binomial(N, α) ≥ Bf) | `SplitAudit.split_product_bound` |
| k = 1: C(N−1,Bh)/C(N,Bh) = 1 − Bh/N | `SplitAudit.hidden_one_step` |
| C(N−k,B)/C(N,B) ≤ ((N−B)/N)^k for 0 < N, k ≤ N, B ≤ N (existing) | `AuditBudget.survival_le_pow` |
| the same three bounds for the event "k attacks released before the first catch" (harm done even if caught later) | `Truncation.split_hidden_bound_prefix`, `Truncation.split_flag_bound_prefix`, `Truncation.split_product_bound_prefix`, from `Truncation.prefix_eq_truncated` |
| attacker who chooses the kind of attack: P(≥ k attacks, never caught) ≤ (1−ρ)^k + P(Binomial(N, α) ≥ Bf) when **every** class has recall ≥ ρ | `ClassAudit.class_flag_bound` |
| N = 100, Bh = 10, k = 5, ρ = 1/2: pre-exhaustion event ≤ 10104934117421/553929902606080 ≈ 0.0182 | `SplitAudit.split_example` |

Definitions a reader needs: `SplitAudit.splitK`, `SplitAudit.catchRule`, `FlagBudget.totSucc`, `FlagBudget.preSucc`,
`FlagBudget.exhLive`, `FlagBudget.flagCount`, `FlagBudget.preAtt`, `FlagBudget.binTail` (the binomial tail by its
recursion; the executable model checks it equals the binomial sum), `ReservedAudit.pU`, `Leakage.val`.

**Reuse and composition** (direction §5C).

- Shared by both protocols, reused unchanged: the game semantics (`Leakage.val`, `AOut`, `attackSet`, `liveInd`,
  `caughtFlag`), the schedule law (`ReservedAudit.pU`, `sum_pU`), and one failure event.
- New shared lemma: `FlagBudget.val_le_potential` / `cval_le_potential` (a supermartingale bound).
  `Leakage.val_le_cval` is its special case W = cval.
- P1-specific: information hiding. `split_hidden_bound` is `ReservedAudit.reserved_leak_bound` applied to `splitK`;
  the protocol-specific obligations were (a) an S-independent certificate of mass ≤ 1 and (b) turning "never caught"
  into "no attack in a reserved round" on the kernel's own transcripts (`SCons`, `totSucc_eq_successInd`, through
  `Leakage.val_congr_on`).
- P2-specific: the budget bookkeeping (`flagCount`, `preAtt`), the two potentials `W1`, `W2` and their one-round
  inequalities `pre_step`, `tail_step`.
- **The composition is a real one.** `split_product_pre` chains `Leakage.seq_transfer` (existing: reduces the
  hidden-schedule game to a game against an S-independent certificate) with `pre_step` (new: bounds that certificate
  game). Connecting obligations, all proved: the certificate dominates the kernel for every S (`splitK_dominated`),
  the blind average of the S-dependent payoff is ≤ C/C times the S-free payoff (`Leakage.blind_audit`), and the
  certificate satisfies the recall inequality. The premise that carries the composition is S-independence of the
  flag law: `dependence_witness` shows the product is false when the flag law depends on the schedule, even with
  the same recall for every schedule.
- **What does not compose, stated precisely.** (i) Imperfect reserved-audit recall with visible flags:
  `ReservedRecall.adaptive_recall_bound` is stated for `AOut Unit` (flags hidden) and its discount lemmas
  (`phi`, `fac`, `phi_live`) are not generic in the leak type. (ii) The deterministic gate model (`Core/Gate.lean`,
  SC-90): no declaration connects a gate trace to this round kernel. (iii) The VCVio defer game
  (`DeferGame.lean`): different history type. None of these is bridged by an assumed lemma.

## 4. Negative controls

| generalisation a researcher might make | witness (Lean-checked value of a concrete kernel) |
|---|---|
| "With monitor recall ρ on every attack the attacker's success is at most (1−ρ)^k." | `SplitAudit.exhaustion_witness`: monitor recall 1, false-positive rate α ∈ (0,1], Bf = 1, N = 2. Attacking in the last round succeeds with probability exactly α, because a flag raised after exhaustion triggers no audit. No flag needs to be observed. (The catch recall after exhaustion is 0; the witness refutes compounding the monitor's recall, not a per-attack catch recall.) |
| "Recall averaged over the kinds of attack in the benchmark can be used in the bound." | `ClassAudit.class_average_witness`: two attack classes with recall 1 and 0 (average 1/2). The attacker who always uses the second is never caught, against a claimed 1/2. `ClassAudit.class_flag_bound` needs ρ below the recall of every class. |
| "The monitor's measured recall is ρ, so ρ can be used in the bound." | `SplitAudit.average_recall_witness`: the monitor catches attacks in round 0 and misses them in round 1. An attacker spread evenly over the rounds is missed half the time (measured recall 1/2); the attacker who picks round 1 is never caught, against a claimed bound of 1/2. |
| "The hidden-schedule bound and the per-schedule recall bound multiply." | `SplitAudit.dependence_witness` (N = 3, Bh = 1, Bf = 2, k = 1): recall is exactly 1/2 for every schedule and history, so `split_flag_bound`'s premise holds, but the false positive in round 0 reveals whether round 1 is reserved. The attacker avoids the reserved round and succeeds with probability 1/2 under each schedule, not C(2,1)/C(3,1)·1/2 = 1/3. |
| "A random schedule protects whether or not it is secret." | `AuditBudget.observable_schedule_nogo` (existing; stated for fixed attack sets, a different formalisation from `val`). The executable model reproduces it on `splitK` with a known schedule. |
| "For the split, take the smaller of the two per-step bounds." | False for the total-attack event: N = 6, Bh = 2, Bf = 1, k = 2, ρ = 1/2, α = 1/4 gives optimum 781/2560 ≈ 0.305 > min(2/5, 1/4). Executable model only (`exhaustion_beats_the_recall_term`), found independently by a reviewer's own programme. |

Scope of these controls: each shows that one stated generalisation fails on one instance. None proves that a premise
is necessary in every formulation.

## 5. Executable example and what an experiment would measure

`numerics/budgeted_audit.py` instantiates `splitK` in exact rational arithmetic: the exact optimum over all attackers
by exhaustive recursion over visible histories (no state reduction), named attackers (constant-rate, last-rounds,
round-r), and a reduced-state programme for larger N that the tests validate against the exhaustive one.
`numerics/test_budgeted_audit.py` (12 checks) confirms: on a grid with N ≤ 5 every Lean bound holds for the exact
optimum; the three Lean witnesses are reproduced; `binTail` equals the binomial tail; on three instances with no
false positives the product bound for the pre-exhaustion event is attained exactly (so it is tight there); and the
Lean numbers
(`split_example`, `hidden_one_step`) match. Results are frozen in `numerics/budgeted_audit/results.json`.

Selected model values (floats; N = 1000, total budget 20, k = 5, ρ = 0.5, α = 0.01):

| Bh | Bf | optimal attacker | last-5-rounds blind attacker | best constant-rate attacker | Lean product bound |
|---|---|---|---|---|---|
| 0 | 20 | 0.0343 | 0.0343 | 0.0313 | 0.0345 |
| 4 | 16 | 0.0745 | 0.0745 | 0.0306 | 0.0785 |
| 10 | 10 | 0.524 | 0.524 | 0.0368 | 0.572 |
| 20 | 0 | 0.904 | 0.904 | 0.904 | 1 |

In the rows shown all-flags is best, the product bound is within 10% of the exact optimum, and the last-rounds
attacker attains the optimum (to the six decimal places computed).

**What an experiment would measure, and which parameter it informs.**

| measurement | informs | needed to connect it | cannot establish |
|---|---|---|---|
| recall at the deployed threshold, per attack type and per history class (early or late, after a flag or not, by task family) | ρ, taken as the minimum over the classes | the red-team suite covers the attack types and histories the deployed attacker can reach; a confidence lower bound per class, not a point estimate | recall on attack types outside the suite; that the minimum over tested classes is the minimum over reachable histories |
| honest-run flag rate at the deployed threshold | α, hence P(Binomial(N, α) ≥ Bf) | flag events on honest rounds are not more frequent than α conditionally on the past (drift and bursts violate this); an upper confidence bound | that an attacker cannot raise the flag rate on rounds it does not attack (the premise is on "flag and not caught", which includes attacker-induced false positives) |
| whether audit selection is observable (timing, queue state, reviewer behaviour) | the hidden-schedule premise of P1 | an explicit list of the attacker's observation channels | absence of unlisted channels |
| whether the flag depends on the reserved schedule (for example skipping a flag audit on a reserved round) | S-independence, needed for the product | inspection of the audit dispatcher | |

With measured (ρ̂, α̂) the bounds are **illustrative** unless ρ̂ is a lower confidence bound for the minimum over
classes and α̂ an upper one; the repository's existing route from estimates to checked certificates is `Core/Cert`
with the preregistrations in `prereg/`, not used here.

**The experiment that tests this bridge** is preregistered as a draft in
[experiments/E1-flag-budget-replay/PREREG.md](../../experiments/E1-flag-budget-replay/PREREG.md): a replay of real
monitor scores (LinuxArena public mirror, 22,215 trajectories, CC-BY-4.0) through the flag-budget protocol, with
recall and false-positive bounds measured on six environments and checked on four others. It has not been run; it
needs the owner's authorisation.

**Two kinds of agreement, kept apart.** The tests show the executable model agrees with the Lean closed forms on
the instances tried. They do not show that any runtime implements `splitK`; no Lean-to-runtime correspondence is
claimed (`trusted_stack/audit.py` is a reference schedule only).

## 6. Assumption audit

| assumption | role in the proof | why needed | kind | how to justify or challenge | does a measurement match its quantifiers? | plausibility | if weakened |
|---|---|---|---|---|---|---|---|
| S uniform over Bh-subsets, drawn before play | makes the blind average of "≥ k attacks, none in S" at most C(N−k,Bh)/C(N,Bh) (`blind_audit`) | the count is for the uniform law | implementation premise | inspect the scheduler and its randomness source | yes, by inspection or a statistical test of the generator | untested for any deployment | a non-uniform law gives a different, possibly much worse, constant |
| S hidden: attack law depends only on the visible history | the certificate is S-independent, so transfer applies | otherwise the attacker avoids S | empirical and implementation | enumerate observation channels; leakage tests | only for listed channels | not identifiable in general (cannot prove absence of side channels) | `Leakage.audit_leak_bound` degrades the bound by the leak's certificate mass; total leak gives 1 (`observable_schedule_nogo`) |
| flag law independent of S (function of visible history and attack bit) | same certificate argument, with flags visible | S-dependent visible flags can reveal S (`dependence_witness`) or correlate catches | implementation | inspect the dispatcher | yes, by inspection | plausible when monitor and scheduler are separate programs; untested | product fails (`dependence_witness`); per-schedule flag bound still holds |
| reserved audit catches an attack with certainty | "never caught" implies "no attack in S" | used by `totSucc_eq_successInd` | empirical | measure audit recall on known attacks | yes, a rate on audited attacks | known to be imperfect in practice | proved only with hidden flags (`ReservedRecall.adaptive_recall_bound`); with visible flags it is open |
| `hrec`: conditional recall ≥ ρ at every history with budget left | one-round supermartingale inequality (`pre_step`) | compounding needs it at each attack, whatever preceded it | empirical, and it is **most of the conclusion** | red-team per history class; adversarially search for low-recall histories | no for an average; partly for a per-class minimum | not identifiable from a fixed benchmark: the attacker chooses the history | no bound is proved; informally the factor per attack becomes the miss probability at the history the attacker picks, which `average_recall_witness` shows can be 1 |
| `hfp`: P(flag and not caught) ≤ α at every history with budget left | one-round inequality for the binomial-tail potential (`tail_step`) | exhaustion is what removes P2's protection | empirical | honest-run flag rates; check for bursts and for attacker-induced flags | partly (see table above) | untested | the exhaustion term grows; at αN ≥ Bf it is about 1/2 or more |
| hard first-come budget | defines exhaustion | it is the protocol | definitional | n/a | n/a | n/a | threshold-ranked or paced budgets are different protocols (backlog item 2) |
| catch is absorbing; base event is "never caught by round N" | payoffs carry `liveInd` | lets caught transcripts be ignored | modelling choice | superseded for `splitK` by the next row | n/a | n/a | n/a |
| "k attacks released before the first catch" has the same value against the attacker stopped after k attacks | `Truncation.prefix_eq_truncated` | turns the event into the one a designer cares about | mathematical (proved for `splitK`: a non-attack is never caught) | the executable model agrees for N ≤ 5 (`prefix_event_has_the_same_optimum`) | n/a | proved | not proved for an arbitrary kernel, nor for `ClassAudit.classK` |

Why `flag_pre_bound` is worth having although `hrec` carries most of it (*interpretation*): the theorem's content is
the compounding against adaptive timing and the exact accounting of exhaustion. Its use is to isolate the unresolved
difficulty in one inequality with stated quantifiers, so that a measurement can be compared with it and found
insufficient (an average) or sufficient (a per-history lower bound), and to support sensitivity analysis in ρ and α.
It does not establish that any monitor satisfies `hrec`.

## 7. Knowledge classification and provenance

| claim | kind | provenance and novelty |
|---|---|---|
| hypergeometric survival of a k-set against a uniform B-subset | mathematical result | established (classical sampling without replacement) |
| adaptivity gains nothing against a hidden schedule | mathematical result | new formalisation of known reasoning (existing in this repository since `ReservedAudit.lean`) |
| (1−ρ)^k from a per-history hazard; binomial tail for exhaustion | mathematical result | established (optional stopping; binomial tail); new formalisation |
| product bound for the split under S-independent flags | mathematical result | composition of existing results; novelty unassessed, no literature review done |
| the three witnesses | mathematical result (finite computations) | new formalisation; the phenomena are folklore |
| "constant-rate red teams understate risk near αN = Bf" | finding in the executable model, not a theorem and not an empirical finding about real systems | composition; the three-round version is `ledger/TMGAC.lean`; novelty unassessed |
| honest usefulness equal across P1, P2, split | modelling choice | follows from the protocols having no block or defer action |
| ρ should be the per-class minimum recall | informal argument | supported by `average_recall_witness`; the measurement recipe itself is untested |

**Sources.** The following were read through an automated fetch of the arXiv HTML on 2026-10-13 (first 100k
characters of each; quotations as returned by the fetch tool, so a person should spot-check them before they are
cited elsewhere):

- Greenblatt, Shlegeris, Sachan, Roger, *AI Control: Improving Safety Despite Intentional Subversion*,
  arXiv:2312.06942v5. Section 3.1.2: upfront auditing audits every submission until the audit budget (2% of
  solutions) is used up. Section 3.2: trusted monitoring audits "the top 2% most suspicious proposals", threshold at a 2%
  false-positive rate. Section 2: "it's a safety failure if even one backdoor is submitted" (k = 1), and the attack
  policy keeps no state between calls. This record's relation: upfront auditing is an observable schedule; trusted
  monitoring at a 2% threshold with a 2% budget is the αN = Bf case of P2 **if** the budget is a hard first-come cap,
  which this record did not verify for that paper.
- Griffin, Thomson, Shlegeris, Abate, *Games for AI Control*, arXiv:2409.07985v2. Section 4: a stock of audit coins,
  c = 0.02·M, decremented per audit; "If the protocol attempts to audit when no audit coins are left, the code is run
  instead"; Blue's thresholds may depend on problems and coins remaining; Red "receives only the null observation".
  Relation: the hard cap here is their coin stock; their Blue can pace thresholds, which this record does not model;
  their Red is strictly weaker than the attacker class here.
- Abstracts only: Bhatt et al., *Ctrl-Z*, arXiv:2504.10374v1 (multi-step agent tasks); Wen et al., *Adaptive
  Deployment of Untrusted LLMs Reduces Distributed Threats*, arXiv:2411.17693v1 (no single action catastrophic).
  These are the settings where k > 1 is the natural event. No claim from their bodies is used.

Nothing in this record is attributed to those papers beyond the quoted protocol definitions.

## 8. Verification status and review needs

See the verification report in the pull request and `HANDOFF.md` for the commit, commands and results. Summary:
Lean statements compile with standard axioms in a full project build; the registry and statement catalogue are
regenerated; the executable checks pass; declaration references in this file are checked by
`tools/check_records.py`. Three model reviewers (two of this model family, one of another) read the plan before
implementation; their objections changed the design (exhaustion term, product theorem, corrected witness) and are
summarised in the pull request. That is not independent human review.

**Review packet: four questions for someone outside the implementation effort.**

1. *Does the model capture the question?* Is a hard first-come flag budget with a stationary threshold the protocol
   you would analyse, or is pacing (thresholds that depend on rounds and audits remaining) essential? Is "at least k
   attack rounds released and never caught by the end" the right failure event, given the unproved truncation step?
2. *Are the assumptions meaningful?* Is per-history conditional recall something a red-team exercise could bound
   from below, and how? Is letting the attacker see every flag too strong, given that the last-rounds attacker needs
   no flag at all?
3. *Does the English match the Lean?* Check section 3's table against `split_hidden_bound`, `flag_total_bound` and
   `split_product_bound`, especially: the flag law's arguments, "while budget remains" meaning fewer than Bf earlier
   flags, and the event `totSucc`.
4. *Would it change a decision?* Would the exhaustion numbers in section 1 change how you set a flag threshold
   relative to an audit budget, or how you constrain a red team (constant-rate against time-aware)?

Status of that review: **pending; no reviewer has been asked.**

```json record-index
{
  "record": "budgeted-audit-vs-adaptive-attacker",
  "base_commit": "e7b4b25",
  "declarations": [
    "ControlStack/Families/F6/SplitAudit.lean::split_hidden_bound",
    "ControlStack/Families/F6/SplitAudit.lean::split_flag_bound",
    "ControlStack/Families/F6/SplitAudit.lean::split_flag_bound_avg",
    "ControlStack/Families/F6/SplitAudit.lean::split_min_bound",
    "ControlStack/Families/F6/SplitAudit.lean::split_product_pre",
    "ControlStack/Families/F6/SplitAudit.lean::split_product_bound",
    "ControlStack/Families/F6/SplitAudit.lean::exhaustion_witness",
    "ControlStack/Families/F6/SplitAudit.lean::average_recall_witness",
    "ControlStack/Families/F6/SplitAudit.lean::dependence_witness",
    "ControlStack/Families/F6/SplitAudit.lean::hidden_one_step",
    "ControlStack/Families/F6/SplitAudit.lean::split_example",
    "ControlStack/Families/F6/SplitAudit.lean::splitK_dominated",
    "ControlStack/Families/F6/SplitAudit.lean::totSucc_eq_successInd",
    "ControlStack/Families/F6/FlagBudget.lean::val_le_potential",
    "ControlStack/Families/F6/FlagBudget.lean::cval_le_potential",
    "ControlStack/Families/F6/FlagBudget.lean::pre_step",
    "ControlStack/Families/F6/FlagBudget.lean::tail_step",
    "ControlStack/Families/F6/FlagBudget.lean::flag_pre_bound",
    "ControlStack/Families/F6/FlagBudget.lean::flag_exhaust_bound",
    "ControlStack/Families/F6/FlagBudget.lean::flag_total_bound",
    "ControlStack/Families/F6/Truncation.lean::prefix_eq_truncated",
    "ControlStack/Families/F6/Truncation.lean::split_hidden_bound_prefix",
    "ControlStack/Families/F6/Truncation.lean::split_flag_bound_prefix",
    "ControlStack/Families/F6/Truncation.lean::split_product_bound_prefix",
    "ControlStack/Families/F6/ClassAudit.lean::class_flag_bound",
    "ControlStack/Families/F6/ClassAudit.lean::class_average_witness",
    "ControlStack/Families/F6/ReservedAudit.lean::reserved_leak_bound",
    "ControlStack/Families/F6/ReservedAudit.lean::reserved_total_le",
    "ControlStack/Families/F6/ReservedAudit.lean::flag_audits_le",
    "ControlStack/Families/F6/ReservedAudit.lean::observable_and_exhausted",
    "ControlStack/Families/F6/ReservedRecall.lean::adaptive_recall_bound",
    "ControlStack/AuditBudget.lean::observable_schedule_nogo",
    "ControlStack/AuditBudget.lean::survival_le_pow",
    "ControlStack/Core/Leakage.lean::seq_transfer",
    "ControlStack/Core/Leakage.lean::val_le_cval",
    "ControlStack/Core/Leakage.lean::val_congr_on",
    "ControlStack/Core/Leakage.lean::blind_audit",
    "ControlStack/Core/Leakage.lean::audit_leak_bound"
  ],
  "definitions": [
    "ControlStack/Families/F6/SplitAudit.lean::splitK",
    "ControlStack/Families/F6/SplitAudit.lean::catchRule",
    "ControlStack/Families/F6/SplitAudit.lean::SCons",
    "ControlStack/Families/F6/FlagBudget.lean::totSucc",
    "ControlStack/Families/F6/FlagBudget.lean::preSucc",
    "ControlStack/Families/F6/FlagBudget.lean::exhLive",
    "ControlStack/Families/F6/FlagBudget.lean::flagCount",
    "ControlStack/Families/F6/FlagBudget.lean::preAtt",
    "ControlStack/Families/F6/FlagBudget.lean::binTail",
    "ControlStack/Families/F6/FlagBudget.lean::W1",
    "ControlStack/Families/F6/FlagBudget.lean::W2",
    "ControlStack/Families/F6/ClassAudit.lean::classK",
    "ControlStack/Families/F6/Truncation.lean::prefSucc",
    "ControlStack/Families/F6/Truncation.lean::stopAfter",
    "ControlStack/Families/F6/ReservedAudit.lean::pU",
    "ControlStack/Core/Leakage.lean::val"
  ],
  "uses": {
    "ControlStack/Families/F6/SplitAudit.lean::split_hidden_bound": ["reserved_leak_bound", "val_congr_on", "totSucc_eq_successInd"],
    "ControlStack/Families/F6/SplitAudit.lean::split_flag_bound": ["flag_total_bound"],
    "ControlStack/Families/F6/SplitAudit.lean::split_min_bound": ["split_hidden_bound", "split_flag_bound_avg"],
    "ControlStack/Families/F6/SplitAudit.lean::split_product_pre": ["seq_transfer", "blind_audit", "splitK_dominated", "cval_le_potential", "pre_step", "val_congr_on"],
    "ControlStack/Families/F6/SplitAudit.lean::split_product_bound": ["split_product_pre", "flag_exhaust_bound", "totSucc_le"],
    "ControlStack/Families/F6/FlagBudget.lean::flag_pre_bound": ["val_le_potential", "pre_step"],
    "ControlStack/Families/F6/FlagBudget.lean::flag_exhaust_bound": ["val_le_potential", "tail_step"],
    "ControlStack/Families/F6/FlagBudget.lean::flag_total_bound": ["flag_pre_bound", "flag_exhaust_bound", "totSucc_le"],
    "ControlStack/Families/F6/Truncation.lean::split_flag_bound_prefix": ["prefix_eq_truncated", "split_flag_bound", "stopAfter_isDist"],
    "ControlStack/Families/F6/Truncation.lean::split_product_bound_prefix": ["prefix_eq_truncated", "split_product_bound"],
    "ControlStack/Families/F6/ClassAudit.lean::class_flag_bound": ["flag_total_bound"]
  },
  "executable": ["numerics/budgeted_audit.py", "numerics/test_budgeted_audit.py", "numerics/budgeted_audit/results.json",
                 "experiments/E1-flag-budget-replay/analyze.py", "experiments/E1-flag-budget-replay/test_analyze.py",
                 "experiments/E1-flag-budget-replay/PREREG.md"]
}
```
