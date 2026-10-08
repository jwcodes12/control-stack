## Verdict

Do not build the full calculus yet.  
Most proposed combinators package classical mathematics; Lean certification does not make them theoretically novel.  
The defensible product is conditional accounting, experiment design, and refutation.  
The existing results do **not** establish sound composition across arbitrary adaptive components.  
SC-01 currently refutes a safety premise; it neither demonstrates full-secret recovery nor certifies general resistance to collusion.

## (a) Theory

**`ControlCert` needs common operational semantics, not just typed fields.** Components must agree on observations, hidden state, permitted policies, failure events, randomness, stopping, and resource consumption. Exact-message recovery and uncaught harmful execution are different events; their bounds cannot simply be multiplied.

You already have much of the appropriate foundation. [TMCERT](./ledger/TMCERT.lean) contains certificate soundness, least Bellman certificates, robust attainment, and concrete-to-abstract coverage. Its `FxGap` distinguishes fixed uncertainty from adversarial selection of different model rows. [ComposeAvg.composedJ_end](/var/tmp/cs-circle/ControlStack/ComposeAvg.lean:57) accepts a **joint** pass-probability bound, avoiding a requirement for independent monitor layers. Repackaging these interfaces is engineering, not another theoretical contribution.

**Local tightness does not imply global completeness.** Different combinators can require incompatible attaining adversaries, distributions, or information access. Arbitrarily loose domination certificates cannot have attaining adversaries. Robust Bellman attainment may require Nature to change models between rounds—more power than a fixed unknown deployment possesses.

A defensible completeness claim would be: for a precisely specified finite protocol language and adversary information structure, the least expressible certificate equals the game value, attained by an admissible strategy. That is substantially harder than collecting sharp inequalities. A meaningful contribution could instead be a strict composition improvement using weaker joint hypotheses, or an impossibility theorem showing which summaries discard information essential for composition.

The actual adaptive scope is:

| Component | What the statements support |
|---|---|
| View products | [covert_bound_lifetime](/var/tmp/cs-circle/ControlStack/CovertChannel.lean:137) permits arbitrary joint transcript encoders. Episode independence is unnecessary, provided the complete observation really lies in the declared product space. |
| Side kernels | [side_bound and dom_pi](/var/tmp/cs-circle/ControlStack/SideChannel.lean:78) cover a fixed kernel and product kernels. They do not establish sequential composition with feedback-dependent side states. |
| Monitor layers | [composedEndToEnd](/var/tmp/cs-circle/ControlStack/ComposeGame.lean:90) supports adaptive content under per-submission bounds and fresh independent trusted randomness. Shared hidden randomness requires a joint bound; multiplying marginal misses is unsound. |
| Coverage | [composedCov_end](/var/tmp/cs-circle/ControlStack/ComposeCoverage.lean:89) uses a **fixed `Apop`**, through `popJ`. Red chooses when to attack; attack content is sampled. Arbitrary history-dependent choices of covered content distributions are not established. |
| Multiple steps | [survival_le and survival_avg](/var/tmp/cs-circle/ControlStack/MultiStep.lean:72) use conditional or posterior hazards. They do not justify substituting marginal ROC recall, nor model arbitrary reconnaissance and retries automatically. |
| Audit budget | [random_subset_survival](/var/tmp/cs-circle/ControlStack/AuditBudget.lean:56) concerns a fixed attack set. The adaptive reduction appears explicitly as an **unformalized modeling remark**, relying on no surviving feedback except “not caught.” |

Naive composition fails even with innocuous marginals: observations \(R\) and \(R\oplus M\), for a fresh uniform bit \(R\), each reveal nothing about \(M\), but jointly reveal it completely. Likewise, two monitors sharing the same blind spot can have joint miss probability \(p\), not \(p^2\).

Missing results include causal side-channel composition; coverage after every reachable history and survival conditioning; schedule leakage; score-triggered audits with benign flags consuming budget; imperfect auditors; delayed shutdown; and joint collusion plus side information. Fixed random auditing and monitor-triggered audit expenditure are different protocols.

**The single next theorem I would fund is leakage-sensitive adaptive auditing.** Start with uniform audit set \(S\), side observation \(Z\) satisfying \(W(z\mid S)\le c(z)\), \(L=\sum_z c(z)\), and a \(k\)-step attacker seeing \(Z\) plus absorbing catch feedback. Prove

\[
P(\mathrm{survive})\le
\min\!\left(1,L\frac{\binom{N-k}{B}}{\binom NB}\right).
\]

Then establish the causal-feedback version under history-uniform domination. This connects two existing components and replaces an all-or-nothing secrecy premise with quantitative sensitivity. The initial result should be inexpensive; the operational adaptive bridge is the real work. Estimate: **2–4 person-weeks**, excluding implementation correspondence. It is an application of known leakage reasoning, not a new information-theoretic principle. Do not promise universal attainment of this coarse bound.

**The necessity catalogue needs narrower labels.**

| Witness | What it actually establishes |
|---|---|
| `attain_embedding` | Optimality over unrestricted encoders on that carrier; not necessity of every modeling assumption. |
| `repair_one_bit_attained` | A particular noiseless side channel defeats the SC-01 target. It does not establish that every kernel above mass 1.11 defeats it. |
| `restore_breaks` | Unaccounted rollback breaks this ledger invariant. It does not exclude safe restoration with external accounting. |
| `varObs_breaks_target` | Arbitrary encoder control over the variable-count carrier defeats the target. Variable counts independent of the secret need not. |
| `correlated_nogo` | Marginal recall cannot justify the hazard product. Independence is not necessary: suitable conditional hazards suffice. |
| `observable_schedule_nogo` | Advance knowledge of the entire schedule permits avoidance when enough unaudited rounds exist. Partial observability is not characterized. |
| `tight_K`, `tight_eps` | Separate coefficient sharpness, not simultaneous attainment of the whole composed protocol. |
| `ComposeBlindSpot` | Population averages alone do not control content-selecting adversaries. It does not make this particular coverage condition uniquely necessary. |

Also, `bsc_lifetime_fails` proves that a **certificate expression** exceeds the threshold, not an attained failure probability. The catalogue provides no systematic witnesses for secret independence, usefulness-sample independence, lineage completeness, implementation correspondence, or every joint-composition premise.

**Novelty:** cardinality guessing bounds, maximal-leakage composition, and the identification \(\log\sum_o\max_s W(o\mid s)=I_\infty\) are established. Feedback requires causal accounting; ordinary whole-sequence product factorization is not justified merely by calling a channel memoryless. [Issa–Wagner–Kamath](https://arxiv.org/html/1807.07878v1), [Massey](https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI532.pdf).

Untrusted monitoring and anti-collusion protocols precede this repo in [Greenblatt et al.](https://arxiv.org/abs/2312.06942); upfront validation, shutdown, and coverage concerns appear in [Ctrl-Z, Appendix E](https://arxiv.org/html/2504.10374v1#A5). Strategic coordination and capability restrictions are studied in [Subversion Strategy Eval](https://arxiv.org/abs/2412.12480). Partially observable control games and safety/usefulness analysis are already [Griffin et al.’s subject](https://arxiv.org/abs/2409.07985). Evidence-to-deployment arguments and their assumptions are central to [Korbak/Clymer et al.](https://arxiv.org/abs/2501.17315).

The plausible contribution is the checked artifact, precise operational bridges, and reusable counterexamples. I would not claim priority for the underlying mathematics.

## (b) Applicability

The likely user is a control-evaluation researcher choosing **an audit allocation, threshold, horizon, or next experiment**. They would run this if it distinguishes “collect more attacks” from “change the protocol” and produces an independently checkable argument. A deployment approver cannot use its current output as authorization.

A generic parameters-to-guarantee CLI has little value if its decisive inputs are user-entered \(K,\epsilon,L,r\) without defensible evidence. It then computes the consequences of the conclusion the user has effectively assumed.

**The near-vacuity has multiple causes.** [CERTIFICATE-DECOMPOSITION.md](/var/tmp/cs-circle/CERTIFICATE-DECOMPOSITION.md) reports:

- LASR closed BigCodeBench: point-estimate risk around 0–0.03 versus certified 0.71–0.83 at \(N=100\). Statistical uncertainty dominates.
- LinuxArena 217: point-estimate risk around 0.97. Sharper intervals cannot rescue that modeled protocol.
- LaStraj: point-estimate risk around 0.996, with only 17 attacks also creating substantial uncertainty.

For one LASR condition, reducing the multiplicity burden changes the reported bound from 0.718 to 0.284. That is material, but it remains post hoc; it requires fresh prospective validation.

With zero observed misses, a one-sided 95% upper miss bound is approximately \(3/n\). A simple 100-opportunity calculation targeting 0.1 therefore needs roughly 3,000 independent samples. This is illustrative, not the exact audit-game requirement. More samples still cannot establish worst-case coverage of an unrestricted attack space. Rectangular uncertainty and excess information granted to Red add separate conservatism.

Useful outputs when certification fails are: point-estimate versus interval-game values; sensitivity to uncertainty and information assumptions; required sample sizes; protocol changes needed for the target; and explicit statements that the target remains unestablished. A large upper bound is not evidence of a large deployment failure probability.

**The assumption ledger should have multiple axes.** “Theorem,” “measurement-refutable,” and “trusted-untestable” mix logical provenance, falsifiability, and evidential status. Record the proposition, scope, quantifiers, dependencies, evidence, confidence procedure, and current status separately. A theorem can depend on unresolved empirical premises. An implementation property can be testable without being established by tests. No failed probe turns a universal claim into a theorem.

The best current measurement loop is SC-01: theory allows side mass only \(65536/59049\); the saved probe has 64/64 bit recoveries and lower endpoint 0.95427; [bit_refutes](/var/tmp/cs-circle/ControlStack/SafetyCaseSC01.lean:78) requires mass at least 1.90854. This rejects the premise under the sampling/model correspondence assumptions. A subsequent unsuccessful probe would mean **not refuted**, not certified isolation.

Benchmark bridges must preserve sampling units and intervention timing. `lastraj_bands.py` and `linuxarena_cert.py` aggregate scores using trajectory maxima. A retrospective maximum does not automatically describe an online monitor catching harm before execution. Existing exporters also contain hard-coded horizons, budgets, and home-directory paths.

**Minimal citable deliverable:** one portable benchmark adapter, one prospectively evaluated protocol decision, exact certificates, a usable sensitivity/sample-size report, and the SC-01 refutation example. Another theorem inventory is insufficient.

## (c) Ceiling

At best, this programme can provide auditable conditional arguments for narrowly specified control protocols: eliminate arithmetic and composition mistakes, expose the cost of adversary information, connect experiments to explicit parameters, and reject premises contradicted by evidence. Structural restrictions can sometimes support meaningful capability-independent guarantees. It cannot establish that the physical observation boundary is complete, that finite attacks cover every deployment strategy, or that an exact-recovery surrogate captures actual harm. Its ceiling is a rigorous component of a safety case, with much of its practical value coming from preventing unjustified positive conclusions.

The three most likely failure modes are:

1. **The key unknowns become inputs.** Users nominate favorable coverage and leakage constants; the checker certifies their arithmetic.
2. **The modeled protocol diverges from execution.** Feedback, shared state, timing, budget consumption, or delayed effects invalidate composition.
3. **The project optimizes the certificate instead of the decision.** Easy formal instances and favorable secret sizes replace meaningful harms and realistic usefulness.

The most likely “true but useless” outcome is a correct tiny exact-recovery probability for an independently sampled secret while one permitted bit reliably communicates “attack now.” [one_bit_coordinates](/var/tmp/cs-circle/ControlStack/CovertNoGo.lean:73) already formalizes the underlying obstruction.

The formal-veneer risk is concrete. [check_sc01_case.py](/var/tmp/cs-circle/tools/check_sc01_case.py) prints “All checks passed” and returns zero even when its verdict is `HYPOTHESIS_REFUTED`; the manifest remains `CONDITIONAL`. Separate execution success, proof validity, evidence validity, and case applicability in machine-readable outputs. Put the failure event, adversary class, unresolved premises, and confidence statement beside the number. Label it **conditional model bound**, not “certified safety.”

## Ranked plan

Efforts are person-time estimates, excluding expensive evaluation runs.

1. **Correct scope and verdict reporting — 2–4 days.** Acceptance: adaptive-coverage and audit claims match their binders; refuted premises cannot produce an ambiguous success status; obsolete review findings are reconciled.
2. **Make the SC-01 refutation independently reproducible — 1 week.** Acceptance: the case checker invokes cache-receipt validation, recomputes statistical endpoints, and reports sampling assumptions and refutation scope.
3. **Build one portable decision tool — 2–3 weeks.** Acceptance: clean-checkout execution takes external counts/configuration and emits certificates, assumptions, decomposition, and target/sample-size sensitivity without home-directory dependencies.
4. **Repair adaptive coverage — 1–2 weeks.** Acceptance: an operational theorem permits history-dependent attack-content laws satisfying coverage at every relevant history; the blind-spot counterexample remains a regression.
5. **Prove leakage-sensitive adaptive auditing — 2–4 weeks.** Acceptance: explicit observation semantics, sound causal composition, hidden/visible limiting cases, and a nontrivial intermediate example.
6. **Run one prospective external-user demonstration — 3–6 weeks.** Acceptance: a researcher uses the output to change an experiment or protocol choice, then evaluates that choice on held-out evidence.
7. **Defer the universal calculus and exhaustive catalogue — revisit after item 6.** Acceptance for restarting: two clients require the same semantic interface. Until then, exclude more adapters, global tightness promises, and attempts to certify the physical boundary.

## Things I checked in files

- [HANDOFF](/var/tmp/cs-circle/HANDOFF-lean-track.md), [ROADMAP](/var/tmp/cs-circle/ROADMAP.md), [REVIEW-PACKET](/var/tmp/cs-circle/REVIEW-PACKET.md), [STACK](/var/tmp/cs-circle/STACK.md), relevant Lean statements, ledger claims, and exported proof declarations.
- [SC-01 manifest](/var/tmp/cs-circle/assurance/sc01-safety-case.json), checker and receipts: independently matched all 18 manifest hashes, cache-source hashes, 64 successes, constant NULL views, and exact lower-endpoint arithmetic.
- Numerical generators, bands, summaries, decomposition, and exporter paths.
- `ScenarioACore.five_episode_core_bound` closes the older carrier-to-core modeling gap; documents still repeat obsolete findings.
- Checkout HEAD was `eb0200e`. I changed nothing and ran no builds. Historical gate/reviewer outcomes remain documentary claims; I did not independently replay them.

## Things I am inferring

Likely adoption, research value, implementation effort, and the proposed theorem’s tractability are judgments. No new composition theorem was proved here, no physical isolation was validated, and no exhaustive novelty search was completed.