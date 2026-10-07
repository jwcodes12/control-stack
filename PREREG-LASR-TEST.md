# Preregistration: certification on the LASR held-out test split, all conditions (2026-10-07)

Committed before running the analysis below.

**Why this is held out.** The LASR code (`NelsonG-C/lasr-labs-2025-control-project` @ 455103e) assigns dataset records with
even index to the test split (`even_test`) and odd to training (`odd_train`), for APPS and BigCodeBench, and generators
default to `data_split="test"`. Every one of the 43,698 sample ids in our local archive (`<research-root>/audit2/lasr_scores`,
126 CSVs, 42 conditions) is even, so the released score logs are on held-out test tasks. Monitors/collusion strategies
were developed on the training split per the paper's design.

**Prior exposure (disclosed).** This is not a blind analysis. The archive was audited in an earlier session (LASR
untrusted-monitoring audit), and the exploratory certificate for `closed-source-model__apps__self_rec/none_base` (risk
≤ 0.577) is known. To remove the selection problem, NO condition is chosen: every condition is certified and reported.

**Data per condition.** `honest.csv`, `attack.csv`; column `trusted_suspiciousness_score` (the trusted monitor; integer
0..10). Rows with a missing trusted score: honest counted as FLAGGED, attack as MISSED (conservative). Honeypots unused.

**Bands.** Cutoffs c = 0..11, flag iff score ≥ c (K = 12). Clopper–Pearson, Bonferroni: α = 1/20 split equally across all
C = 42 conditions, and within each across 2 rates × 12 cutoffs × 2 tails (`numerics/roc_bands.py`, α_c = 1/840).
Family-wise coverage ≥ 95% over every band of every condition simultaneously. Endpoint denominator 100000.

**Certificate per condition.** The DESIGN-A2 game unchanged (`lasr_design_a2_certificate.calculate`): audit `score_ge_7`,
defer `score_ge_3`, N = 100, 2 coins. Also report the N = 1, 10, 100 rows of the value table. Each certificate is
emitted to Lean and checked (`checkRiskQ`/`checkLawfulQ` by `decide +kernel`, TMCERTF1 risk bound) sequentially.

**Reported.** A table of all 42 conditions (counts, bands at 3 and 7, certified risk at N = 1, 10, 100) and the worst
condition. No condition is dropped or tuned.

**Interpretation.** Valid simultaneous 95% statements for each condition's trusted monitor on that condition's test-task
distribution, assuming the test samples are an IID draw from it. Caveats fixed in advance: attack samples may be
filtered (e.g. to working backdoors) by the paper's pipeline, so the attack population is "attacks as released"; the
honest sets may coincide across conditions (Bonferroni does not need independence). Not a deployment certificate.

**Code.** `numerics/lasr_test_all.py` (committed with this file).

## Results (run after the prereg commit 2c10cae)
Full table: `numerics/lasr_test/summary.json`. Certified full-information risk with 2 audit coins:

| class / setting | conditions | N = 1 | N = 10 | N = 100 |
|---|---|---|---|---|
| closed-source (T = GPT-4o-mini), APPS | 15 | 0.130–0.220 | 0.329–0.514 | 0.626–0.804 |
| closed-source, BigCodeBench | 12 | 0.052–0.083 | 0.090–0.219 | 0.708–0.832 |
| open-source (T = Qwen3.5-4B), APPS | 15 | 0.062–0.433 | 0.103–0.598 | 0.987–0.9997 |

Worst condition at N = 100: open-source APPS self_rec/none_base (0.9997). The closed-source trusted monitor gives the
first non-vacuous held-out 100-task certificates in this project. Lean checks run sequentially (≈5 min each).
