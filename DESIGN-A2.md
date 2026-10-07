# DESIGN-A2: a sampled-ROC certificate for a 100-problem, 2-coin game

**Status:** design note plus exact-rational integration fixture; not a confidence claim, theorem, or deployment certificate.

## Goal

Turn labelled monitor scores into a finite, auditable uncertainty set, then use the TMCERTF1 rational checker to bound catastrophe risk for one Blue policy against three Red classes: a memoryless fixed attack rate, a clock-aware policy, and the full-information Red. The first implementation target is 100 problems and two audit coins. The current repository has no labelled score sample from a deployment, so the numerical fixture below is synthetic and must not be interpreted as an empirical guarantee.

## Proposed measurement pipeline

1. **Freeze the evaluation data.** Collect independent safe and backdoor-labelled score samples from the exact monitor, task distribution, and scaffold to be covered. Record sample sizes, label provenance, sampling unit, score ties, and any task strata. Split policy development data from the certification sample. A threshold policy selected after looking at the certification sample must use a band simultaneous over every candidate threshold.
2. **Predeclare the threshold grid.** Sort the distinct score values and group ties. Each operating point specifies a threshold and a fixed tie rule (all equal scores on one side, or a predeclared randomized tie rule with a rational coin probability). The same grid is used for audit and defer thresholds. This certifies only those choices; it does not silently interpolate to unobserved thresholds.
3. **Compute simultaneous rational bands.** At each threshold, count false positives among safe samples and true positives among backdoor samples. For each Bernoulli rate, compute two-sided Clopper–Pearson limits with a Bonferroni tail allocation of `alpha/(4K)`, where `K` is the number of predeclared operating points. Round the lower endpoint down and upper endpoint up to a fixed rational grid. The exact binomial tail sums and the endpoint comparison are rational; the union bound gives family-wise coverage at least `1 - alpha` across both rates and all `K` thresholds. Keep the raw counts and rounded endpoints in the audit artifact. If threshold points are selected adaptively, include the full candidate set in `K`. The reusable implementation is [`numerics/roc_bands.py`](numerics/roc_bands.py); its synthetic CLI demonstration is only a software exercise, not sample evidence.
4. **Build the finite interval game.** At each horizon/state/action row, use the relevant threshold-rate intervals and ROC intervals. Retain the nesting constraint that the audit threshold is at least as selective as the defer threshold, so `TPR_a <= TPR_d`. The risk row expression is affine in the three uncertain coordinates that enter it: audit false-positive rate `qa`, audit TPR `TA`, and defer TPR `TD`. Clip their rational interval box by `TA <= TD`, then enumerate every vertex, including vertices on the diagonal boundary (filtering only the original box corners would be unsound). There are at most twelve vertices when `qa` is an independent interval and the only cross-coordinate constraint is `TA <= TD` (up to six vertices for the clipped two-dimensional TPR rectangle). A single model index among these row vertices may be selected independently at each row, which is a rectangular overapproximation of the joint uncertainty set. It is conservative when thresholds share a common ROC curve. The defer FPR interval also enters the separate honest-usefulness calculation. If the measured set has additional nonlinear coupling that matters, use a proved hull/coverage argument or keep the full coupled model set; do not assume independent endpoints imply a valid global curve.
5. **Produce and check the certificate.** Compute the least supersolution table by backward dynamic programming using exact rationals. Serialize `cat`, `K`, and `V` in the dimensions consumed by `checkRiskQ`; run `checkLawfulQ` on the same rows and close each Boolean checker result with `decide +kernel`. This is a concrete instance of the already verified checker, not a new theorem. The rational table yields a bound against every Red policy and every row-wise model selection in the finite uncertainty set. Compute honest expected used solutions separately from the GAC recurrence and report it beside risk; `checkRiskQ` alone does not certify usefulness.

## Exact-rational integration fixture

[`numerics/design_a2_certificate.py`](numerics/design_a2_certificate.py) builds a small, fully explicit interval game using only `fractions.Fraction`. It uses 100 problems, two coins, audit FPR `1/50` when a coin remains (zero at zero coins), defer FPR `49/100`, and the illustrative ROC vertices `f(q)=min(1,2q)` and `f(q)=min(1,3q)`. The vertex selector is allowed to vary by row, so the certificate covers more than a single globally fixed slope. These endpoints are assumptions for exercising the table format; they are not derived from samples.

The script writes [`numerics/design_a2_certificate.json`](numerics/design_a2_certificate.json), with exact rational arrays matching `checkRiskQ`'s `N=100, states=3, actions=2, models=2` inputs, and [`numerics/design_a2_value_table.csv`](numerics/design_a2_value_table.csv), with all 101 horizon rows. Its current run computed 1,200 certificate inequalities and produced:

- exact rectangular full-information risk upper bound: `V[100, 2 coins]` in the JSON;
- fixed-rate witness on the `1/100` beta grid: beta `37/50`, risk about `0.33281`;
- clocked witness that attacks only in the final 50 problems: risk about `0.31822` (a witness, not the optimum clocked policy);
- honest expected used solutions: about `52.4641` of 100;
- full-information bound: about `0.45051`.

These approximate decimals are for reading only; the generated artifacts store exact fractions. The large gap between the full-information bound and the restricted witnesses is an expected cost of quantifying over the larger Red class and row-wise uncertainty. The fixture is not evidence that any real monitor has this ROC.

The next data-backed run should substitute sample-derived rational interval endpoints and enumerate the clipped-box vertices above. Let `T` be the largest vertex count at any row (at most 12 under the stated three-coordinate model); use `T` model indices with row-wise selection. At 100 problems, 3 coin states and 2 actions, that is `600T` risk inequalities and `600T` lawfulness rows, each with at most 3 successor terms. At `T=12`, this is 7,200 of each. This is small as a mathematical table; the Lean source encoding and kernel reduction are the main implementation costs.

## Empirical archive pipeline demonstration (2026-10-07)

The local `proofledger/audit2/lasr_scores` archive contains labelled per-sample trusted-monitor scores from LASR Inspect runs. The reproducible example uses `closed-source-model__apps__self_rec/none_base`: 633 honest samples and 240 attack samples, score in `{0,…,10}`. `numerics/lasr_score_bands.py` computes bands at every integer cutoff, with ties kept together, and records the two input CSV hashes in [`numerics/lasr_selfrec_nonebase_roc_bands.json`](numerics/lasr_selfrec_nonebase_roc_bands.json). The threshold grid is fixed by the score scale; the Bonferroni allocation covers both rates at all 12 cutoffs for this condition.

For the illustrative nested pair `audit score ≥ 7`, `defer score ≥ 3`, the simultaneous intervals are:

| rate | observed count | interval |
|---|---:|---:|
| audit FPR | 0 / 633 | `[0, 1079/100000]` |
| audit TPR | 70 / 240 | `[644/3125, 38901/100000]` |
| defer FPR | 33 / 633 | `[289/10000, 2127/25000]` |
| defer TPR | 218 / 240 | `[8373/10000, 239/250]` |

`numerics/lasr_design_a2_certificate.py` clips the TPR interval box by `TPR_audit ≤ TPR_defer`, enumerates its four exact TPR vertices crossed with the audit-FPR endpoints (eight models), and emits the 100-problem/two-coin table. `numerics/emit_lasr_design_a2_lean.py` assembles that table with the frozen TMCERTF1 statement and its proof. The resulting `checkRiskQ` and `checkLawfulQ` instances both compiled by `decide +kernel` in the shared Lean project (4,800 risk inequalities); a further Lean theorem applies TMCERTF1 soundness to bound every history-dependent Red policy and admissible row selector. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all three theorems. The full-information rectangular risk upper bound is about `0.577300`. The separate simple honest-reward floor is `22873/250 = 91.492` of 100, using only the defer-FPR upper endpoint; this is not a `checkUseQ` certificate.

Reproduce with `python numerics/lasr_score_bands.py <honest.csv> <attack.csv> --condition <name> --output numerics/lasr_selfrec_nonebase_roc_bands.json`, then run `python numerics/lasr_design_a2_certificate.py` and `python numerics/emit_lasr_design_a2_lean.py`; compile the emitted file from `~/research/alignment-contrib/lean/StabilityDebate` with `lake env lean ~/research/control-stack/numerics/lasr_design_a2_certificate.lean`.

This is a real-data pipeline demonstration, **not a deployment certificate or a valid claimed 95% confidence guarantee**. The archive is not established as a predeclared held-out IID sample from the target deployment; the condition was selected from a larger archive, and no adjustment across conditions was made. The confidence interpretation is conditional on the sampling assumptions in §1. The exact checker certifies the finite rational game induced by these intervals; it does not prove those intervals cover a deployment monitor or that the LASR task distribution matches the intended 100-problem GAC application.

## Assumptions and limits

- The samples represent the deployed task distribution and monitor version; labels are correct; the backdoor class used for sampling covers the deployment class of concern.
- The confidence statement is conditional on the sampling protocol and its independence assumptions. Distribution shift, adaptive data collection, label error, and unrepresented backdoors are not discharged by the checker.
- The two-coin GAC abstraction, threshold semantics, catastrophe event, and task horizon match the intended protocol. The existing `TMGACF1` result supplies the recurrence bridge for its stated model; the finite interval table must still be checked against the concrete GAC rows.
- A confidence band over operating points does not establish scaffold enforcement, state coverage, or the identity between a sampled score and a deployment monitor view.
- The current exact fixture has not been passed through Lean's `decide +kernel`; no new theorem or frozen claim is made in this phase.

## Cost estimate

For `K` operating points, the statistical work is `O(K)` exact binomial interval calculations after the sample counts are collected. A rational outward-rounding grid of denominator `D` needs `O(log D)` endpoint searches per tail; exact binomial sums dominate for large sample sizes. The risk table for the intended game has 606 certificate values. With `T` vertices per row, the risk checker has `600T` inequalities and the lawfulness checker has another `600T` rows, each with no more than three successor terms; at the stated upper bound `T=12`, that is 7,200 of each. The JSON/Lean input should remain in the low-megabyte range for rational endpoints of a few dozen digits.

Planning allowance on a 2-core machine: about 0.5–2 engineer-days to validate the data protocol, implement and review exact bands and tie handling; 0.5–1 day to adapt the interval rows to the GAC adapter and emit checker inputs; and a half day to profile Lean elaboration/kernel reduction and shrink tables if needed. A first `decide +kernel` run could take seconds to several minutes and perhaps hundreds of MB, but this is an unmeasured engineering estimate. Budget one working day for debugging the first table-to-Lean encoding. The monitor evaluation sample collection and label review are separate, domain-dependent costs and cannot be estimated without a target system and sample plan.

## Next decision point

Obtain the labelled validation sample and freeze the operating-point grid. Then replace the illustrative endpoints, run the exact table generator, measure the concrete `decide +kernel` cost, and report the risk/usefulness pair with the confidence level and its coverage assumptions. Do not call the result a deployment certificate until row coverage and scaffold assumptions are independently established.
