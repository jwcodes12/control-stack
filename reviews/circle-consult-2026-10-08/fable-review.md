# Circle consultation: independent review (Fable, 2026-10-08)

Read-only review of `/var/tmp/cs-circle` at `eb0200e`. No build was run; "proved" below means I read the statement and the `#print axioms` line, not that I re-checked the kernel.

## Verdict

1. The proposed `ControlCert` calculus is, mathematically, a union bound, a product of cardinalities, the maximal-leakage guessing bound, a hazard product and sampling-without-replacement. None of the combinators is new; what is new is the operational-game formalisation and the refutation lemmas.
2. There is no cross-component composition theorem in the repo today (side channel x monitor x audit x multi-step). Each file quantifies over a different adversary class and a different event; a "whole-calculus completeness theorem" cannot be stated until those classes are unified, and unifying them is where the real difficulty lives.
3. The necessity catalogue is honest per combinator but has at least five load-bearing assumptions with no witness, and no witness concerns the composed bound.
4. The benchmark certificates are vacuous at N=100 for two different reasons, and only one of them is statistical. The other is the protocol (defer without incrimination compounds), and no sample size fixes it.
5. The 20% that matters: the typed assumption ledger with refutation lemmas, the vacuity diagnoser, one eval-log bridge, and a write-up whose headline results are the negative ones. The general calculus, the benchmark automation for three suites, and the VM race to reinstate 2^-16 are out.

## (a) Theory

**Is a certificate calculus a contribution?** Not as stated. Map each proposed combinator to what it is:

| combinator | Lean | what it is |
|---|---|---|
| episodes/lifetimes multiply view spaces | `covert_bound_lifetime` (`ControlStack/CovertChannel.lean`) | `|Π V_e| = Π |V_e|`; the bound itself is `P_guess ≤ |V|/|M|`, i.e. Issa–Wagner–Kamath's guessing characterisation of maximal leakage with `L(M→V) ≤ log|V|` |
| side kernels multiply domination masses | `side_bound`, `dom_pi` (`SideChannel.lean`) | `Σ_o max_s W(o|s) = exp L(S→O)` (the file says so). `side_bound` is `P_guess(M | V,O) ≤ exp(L(M→(V,O)))/|M|` plus the chain rule `L(M→(V,O)) ≤ log|V| + L(S→O)`. `dom_pi` is additivity of maximal leakage over independent channels (IWK 2020) |
| monitor layers compose | `composedEndToEnd`, `composedPop_end`, `composedCov_end` | a product that holds because fresh coins are built into the game (the repo's own `COMPOSITION-N1-UMPROT.md` says "novelty is modest"); `coverage_transfer` is a linear transfer under `a ≤ K q + e`, the same shape as the hockey-stick/`SoftHockey` bound already in the stack |
| multi-step uses hazard products | `survival_le` (`MultiStep.lean`) | `Π(1−c)` under a uniform conditional hazard; textbook |
| audit budget uses the hypergeometric | `random_subset_survival`, `survival_le_pow` (`AuditBudget.lean`) | `C(N−k,B)/C(N,B) ≤ ((N−B)/N)^k`; sampling without replacement dominates with replacement |

Writing these as typed Lean combinators is engineering, not theory. The repo's own related-work audit (`reviews/related-work-2026-10-07.md`) reaches the same conclusion for Layer 1 ("modest classical results"), and the Lean-track additions do not change it.

What would make it non-trivial, in descending order of value:

1. **A composition whose hypotheses are weaker than the conjunction.** Today every bound needs its own full hypothesis set and they do not even share an adversary. Example of a real result: a bound on a k-step attack against a *score-triggered, budgeted* audit where Red observes whether each action executed (deferred or not). `AuditBudget.observable_schedule_nogo` shows survival 1 when the schedule is observable; real protocols leak partial schedule information through execution outcomes. The positive result in between does not exist in the repo and is the one theorem that would matter for monitor-side protocols. TMCERT's DP (`checkRiskQ`, full-information Red, tightness (T)) already computes this exactly for a fixed finite game, so a closed-form combinator would be *looser* than what exists; the gap is not a missing formula but an untestable row-coverage premise.
2. **An impossibility result at the level of the whole case.** The strongest results in the repo are already negative (`ComposeBlindSpot`, `correlated_nogo`, `observable_schedule_nogo`, `repair_one_bit_attained`, `varObs_breaks_target`, UMDEFER's no-go). A theorem of the form "no capability-free certificate below X exists for any protocol with property P at horizon N" (the UMUSEF1 `α₀·u ≤ X` obstruction is the one instance) is worth more than ten sound combinators.
3. A completeness theorem "for the whole calculus" is not well-posed until the adversary classes are unified. `covert_bound` quantifies over all encoders with a shared seed; `MultiStep` over history-dependent policies with no seed; `AuditBudget` over fixed attack sets with an informal adaptivity argument in a comment; `composedEndToEnd` over VCVio generators. Per-combinator tightness (which the repo has) does not compose into calculus-level tightness, because the attaining adversaries live in different games.

**Soundness under adaptive adversaries across components.** Verified by reading:

- `SideChannel.dom_pi` assumes per-episode kernels act independently given the side states ("no feedback from side outputs into later side states", file header). A page cache carries state across episodes, so this hypothesis is false for the measured channel. The fix is cheap and known: adaptive composition of maximal leakage gives `Σ_{o₁,o₂} max_s P(o₁|s)P(o₂|s,o₁) ≤ (Σ_{o₁} max_s P(o₁|s)) · max_{o₁} Σ_{o₂} max_s P(o₂|s,o₁)`, so certificates still multiply with history-dependent per-episode masses. This is the one theorem I would prove first; it is a few days of Lean and removes a hypothesis the deployment cannot meet.
- `MultiStep.survival_le` assumes κ is a conditional rate given the full history. `correlated_nogo` correctly shows marginal rates fail. But nothing links κ to a measured ROC: the measurement is a marginal. So the hazard combinator can only ever be fed by a hypothesis, never by data.
- `AuditBudget` assumes an audit catches with certainty and that honest false positives do not consume the budget. Both are false for trusted monitoring; TMCERT models coin consumption and is the right object. Composing `AuditBudget` with `MultiStep` naively (survival ≤ (1−B/N)^k · (1−c)^k) is unsound when the audit decision depends on the same score the monitor uses: the events are not independent. No theorem in the repo says this; it should be a witness.
- **Joint collusion + side channel** is absent. The untrusted monitor in UMPROT sees the mediated view `z`; if it also sees a side observation `o`, the domination constant becomes `L · Σc`. This is a one-page theorem on top of `composedJ_end` (bad-row joint pass `≤ L·Σc·h_ω`) and is the only result that would actually tie the structural scenario to the monitor scenario. It is cheap, but it multiplies an unmeasurable (L) by a currently refuted one (Σc), so its value is structural, not numerical.

**Is the necessity catalogue honest?** Per witness:

- `attain_embedding`: shows `|V|/|M|` is exact. Honest.
- `repair_one_bit_attained`: shows a specific kernel of mass 2 breaks 2^-16. It shows the side-certificate hypothesis cannot be dropped at the design point; it does not show mass ≤ 1.11 is necessary (the "sufficient direction only" caveat is in the file). Honest with the caveat.
- `restore_breaks`, `varObs_breaks_target`: necessity for the model invariant. Honest.
- `correlated_nogo`: shows marginal ≠ conditional. Honest but elementary.
- `observable_schedule_nogo`: honest but trivial; the interesting regime (partially observable, score-triggered) has no witness.
- `tight_K`/`tight_eps`: attained for a specific τ; honest as "cannot be dropped for general τ".
- `ComposeBlindSpot`: honest and the most useful one.

Assumptions in `assurance/sc01-safety-case.json` and the compose files with **no witness**: `secret_independence` (a secret equal to the seed is recovered w.p. 1; trivial to add), `independent_lifetimes` (perfectly correlated lifetimes pass the 63/64 gate w.p. ≈ p, so `false_pass_le`'s 1/80 becomes 0.9; trivial to add and important because the usefulness half is the only conjunct currently not refuted), `trusted_lineage`, the fresh-coins hypothesis of `ComposeGame` (the latent-bit counterexample is in prose in `COMPOSITION-N1-UMPROT.md`, not in Lean), the fixed trace length `L` in `core_bound`, and "catching any step ends the attack" in `MultiStep`. None of the witnesses concerns a composed bound.

**Novel vs known.** Not new: the counting bound, the maximal-leakage guessing bound and its additivity (Issa, Wagner, Kamath, IEEE T-IT 2020; adaptive composition: Issa and Wagner), hazard products, hypergeometric audits, the defer-and-resample dynamics (Ctrl-Z, Bhatt et al. 2025), the untrusted-monitoring game and its POSG recursions (Greenblatt et al. 2023; Griffin et al. 2024, already bridged by TMGAC), multi-step attacks against audit budgets (Wen et al. 2024, "Adaptive deployment of untrusted LLMs", analyses essentially `AuditBudget`'s regime; Mallen et al. 2024 subversion-strategy evals estimate the same quantities statistically), and the three-claim structure of a control safety case (Korbak, Clymer et al., arXiv:2501.17315: elicitation, no degradation, conservative extrapolation). The proposed typed ledger is a formalisation of those three claims; it should cite them as its source. Genuinely new and modest: a machine-checked operational-game formalisation with explicit adversary quantifiers (the related-work audit found none), and the pattern "theorem names the statistic that refutes its hypothesis" (`bit_refutes`), which produced the repo's best empirical result, a negative one.

## (b) Applicability

**Who would use the tool.** For a deployment decision at a lab: nobody today. Lab control teams decide on Greenblatt-style control evals with simulated red teams and Pareto plots; their binding uncertainties are elicitation and transfer, which the ledger would tag TRUSTED-UNTESTABLE. The tool's output for any realistic LLM protocol would be "certified risk ≈ 1" or "conditional on L, r and coverage, which you cannot measure". Two groups could use it for a different decision: (i) safety-case authors (AISI-style) who need an auditable assumption list with a refutation experiment per assumption; (ii) eval designers who want a sample-size and horizon calculator before running an expensive red team. What would change the answer: a client whose honest task actually fits a finite schema channel (SC-01's eight-fault repair is not that client; 64/64 on a 0.25 s programmatic task says nothing about agents).

**N=100 vacuity: artefact or fundamental?** Both, and the owner's framing ("statistical margins") is half right. Verified in `CERTIFICATE-DECOMPOSITION.md` and `numerics/lasr_test/summary.json`: for closed/BigCodeBench/acausal (183/183 deferred, point estimate 0.000 at every horizon) the certified 0.72 at N=100 is margin, and predeclaring one condition and two cutoffs drops it to 0.28; the rule of three says 1,000 to 3,000 attack samples for ≈ 0.1. That part is fixable by design, and cheaply, but needs fresh data (the LASR release has no unseen condition, per the same file). For LinuxArena (`numerics/linuxarena/summary.json`: point estimate 0.97 at N=100, certified 0.99999) the cause is the protocol: a deferred attack is not incriminated, so a full-information Red retries each round and the risk compounds as 1 − TPR_lower per attempt. No sample size fixes that; only incrimination on defer, resampling, or a budget that scales with N. The tool should say which regime a certificate is in. That diagnosis is the most useful thing the benchmark pipeline can output, and it does not exist yet as a tool (the decomposition is a post-hoc script).

**What is useful when the bound is vacuous.** (1) The regime diagnosis above. (2) `n_needed(target, horizon, cutoffs)` from the exact binomial, and `B_needed(N, target)` from the game. (3) A refutation statement rather than a bound. (4) The attained lower bound (the witness Red) next to the upper bound, so the reader sees the gap.

**Is the loop "theory says what to measure" useful?** Yes, with one honest restriction: it returns refutations or "not refuted at power X" for adversarial quantities, and calibrated parameters only for honest-side quantities (FPR, defer rate, usefulness; cf. the A.2 table in `reviews/roadmap-consult-2026-10-08/opus-review.md`, which I agree with). The best demo already exists: `bit_refutes` + `PREREG-SC01-CACHE.md` + `tools/check_sc01_case.py` step 5, verdict HYPOTHESIS_REFUTED from 64/64 with a theorem fixing the threshold (2p > 65536/59049). Next-best demos, both cheap: a preregistered dependence test for `independent_lifetimes` (needs the witness first), and a probe that lets the receiver observe the episode count (`varObs_breaks_target` says what to look for).

**Minimal citable deliverable.** A 10 to 15 page paper plus repo: the VCVio protocol games with end-to-end bounds, the TMCERT checker with the 42 LASR certificates, the SC-01 case with its refutation, and the no-go catalogue in one table. What a researcher would run: one command that takes an Inspect eval log, emits bands, a certificate, a Lean check, the regime diagnosis and the assumption ledger. They will cite the negative results and the refutation pattern, not the bounds.

## (c) Honest ceiling

**Ceiling.** At best this programme is a machine-checked accounting layer for control safety cases: every number traces to a theorem with typed hypotheses; honest-side parameters get certified bands; adversarial parameters are named as untestable rather than silently estimated; each named assumption has a predeclared experiment that can refute it; and a small set of no-go theorems tells protocol designers what no amount of data can certify. It will not produce positive deployment-grade guarantees for LLM agents, because the binding hypotheses (complete observation, L, r, content coverage) are untestable in principle, and the design points that are provable (finite schema channels, 2^-16) cannot carry a useful agent workload.

**Three ways it ends up useless or misleading.** (1) False precision: "P ≤ 2^-16" or "0.115 per task" quoted without the conditional list, by the owner or by a reader. (2) The calculus optimises for what is provable (view counting) while any real deployment drifts to free text, where every hypothesis is UNRESOLVED; the Lean grows, the client set stays empty. (3) Combinator sprawl: more sound-and-tight combinators, each with its own adversary class, none composed, none consumed.

**Most likely "true but useless".** `sc01_case` is true of a model in which the receiver sees exactly the gateway transcript. Every real host gives the receiver more (the repo measured one bit in 64/64 trials with the gateway at constant NULL). The theorem is correct and its conclusion applies to no system; the VM pair will move the refutation to a smaller channel, not remove it, and the design point tolerates no clean bit (`repair_one_bit_attained`).

**Formal veneer risk.** Real. Framing rules: never print a bare bound; print "≤ X CONDITIONAL ON {typed list}" with the TRUSTED-UNTESTABLE set in the headline; print the refutation status and the attained lower bound beside it; label every capability-free bound with the adversary class it quantifies over; and say "model" in every claim string (the covert manifest's claim currently lacks that qualifier, per `REVIEW-PACKET.md` §4).

**20/80 cut.** In: typed ledger with refutation lemmas; missing witnesses; adaptive side-kernel composition; vacuity diagnoser plus sample-size calculator; one eval-log bridge; the write-up. Out: a general `ControlCert` with calculus-level completeness; bridges for all three benchmark suites; new closed-form combinators that TMCERT's DP already dominates; the Python/Lean refinement proof; racing VM isolation to reinstate 2^-16 unless a usefulness-relevant finite-channel client appears.

## Ranked plan

1. **Typed assumption ledger.** Every manifest assumption tagged THEOREM / REFUTABLE(statistic, lemma, experiment) / UNTESTABLE; checker prints the UNTESTABLE set in the verdict line. Acceptance: `check_sc01_case.py` and `tools/assurance.py` emit the three-way split for all 46 manifests with no untagged item. 2–3 days.
2. **Missing witnesses in Lean**: correlated lifetimes break `false_pass_le`; seed-correlated secret breaks `covert_bound`; latent-bit example breaks `composedEndToEnd` without fresh coins; naive `AuditBudget × MultiStep` product is unsound with shared scores. Acceptance: each a standard-axiom theorem listed in the manifests. 3–5 days.
3. **Adaptive side-kernel composition** replacing `dom_pi`'s independence: mass ≤ Π_e max_hist Σ_o c_e(o|hist). Acceptance: `side_bound_adaptive` proved; `ScenarioASide` restated on it; checker updated. 2–4 days.
4. **Vacuity diagnoser + calculator**: for a certificate, report margin share vs protocol-compounding share vs monitor share, `n_needed`, `B_needed`; reproduce the `CERTIFICATE-DECOMPOSITION.md` table. Acceptance: table reproduced to 3 decimals; LinuxArena classified "protocol", BigCodeBench "margin". 3–5 days.
5. **One eval-log bridge** (Inspect format) → bands → certificate → Lean → ledger, one command. Acceptance: a stranger runs it on a LASR-style log in under 30 minutes without reading the repo. 1 week.
6. **UM × side-channel bridge** on `composedJ_end` (bad-row pass ≤ L·Σc·h_ω). Acceptance: theorem proved; stated as structural, not numeric. 2–3 days. Optional.
7. **Write-up** with the no-go table and the SC-01 refutation as headline results, citing IWK 2020, Griffin et al., Wen et al., Korbak et al. Acceptance: a control researcher outside the project reads it and names one thing they would do differently. 1–2 weeks.
8. **Human review** of the specification (`REVIEW-PACKET.md` is ready). Blocked on the owner.

## Things I checked in files

- `/var/tmp/cs-circle/HANDOFF-lean-track.md`, `ROADMAP.md`, `REVIEW-PACKET.md`, `STACK.md`, `CERTIFICATE-DECOMPOSITION.md`, `CATASTROPHE-SPEC.md`, `DESIGN-A2.md`, `COMPOSITION-N1-UMPROT.md`, `PREREG-SC01-CACHE.md`.
- Lean statements and headers: `ControlStack/CovertChannel.lean`, `SideChannel.lean`, `ScenarioASide.lean`, `SafetyCaseSC01.lean`, `ScenarioACore.lean`, `LifetimeLedger.lean` (first 100 lines), `MultiStep.lean`, `AuditBudget.lean`, `ComposeCoverage.lean`, `ComposeBlindSpot.lean`, `ComposeGame.lean` (`composedEndToEnd`), `ComposeAvg.lean` (header).
- `assurance/sc01-safety-case.json` (assumption list and statuses), `tools/check_sc01_case.py` (all five steps, the refutation arithmetic), `tools/assurance.py` (categories and base assumptions).
- `numerics/design_a2_certificate.py`, `numerics/linuxarena_cert.py`, `numerics/lasr_test/summary.json` (risk at 1/10/100), `numerics/linuxarena/summary.json` (0.99999 at N=100), `numerics/linuxarena_split/summary.json`, `numerics/stat_audit.json`, `numerics/lastraj_certificate.lean` (TMCERTF1 header).
- `gateway/scenario/results/local-cache.json` (probe trials, constant NULL view).
- `reviews/related-work-2026-10-07.md`, `reviews/roadmap-consult-2026-10-08/synthesis.md` and `opus-review.md`, `reviews/final-review2-sol.md` (tail).
- No `ControlCert`, necessity-catalogue or circle draft exists in the repo (grep); the plan is only in the prompt. `reviews/circle-consult-2026-10-08/astra.log` is empty.

## Things I am inferring

- That the Lean files compile and the differential test passes: I did not run `lake` or `difftest_core.py`.
- The literature mapping (IWK 2020 guessing characterisation and additivity; Issa–Wagner adaptive composition; Wen et al. 2024; Mallen et al. 2024; Korbak et al. 2025) is from memory plus two web searches that confirmed the IWK and Korbak et al. references; I did not read the adaptive-composition paper's exact theorem for this review, and the inequality I state for adaptive side kernels is my own derivation from the closed form, not checked in Lean.
- "Nobody at a lab would use the tool for a deployment decision" is a judgement about current practice, not a survey.
- The regime split of the N=100 vacuity (margin vs protocol compounding) is inferred from the point-estimate columns of the decomposition table and the TMCERT game structure; I did not re-run `certificate_decomposition.py`.
- Effort estimates assume the current Lean/Mathlib tooling and one experienced Lean author.
