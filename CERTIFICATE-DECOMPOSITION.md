# Where the certified risk comes from (post hoc, 2026-10-07)

Descriptive analysis of the preregistered certificates, NOT a certificate. Script: `numerics/certificate_decomposition.py`
(point-estimate game: every rate fixed at its observed proportion; same DESIGN-A2 game). LASR table:
`numerics/lasr_test/decomposition.json`.

## Point estimate vs certified (2 audit coins, full-information Red)
| run | N=1 point / certified | N=10 | N=100 | dominant source |
|---|---|---|---|---|
| LaStraj (7/3) | 0.059 / 0.428 | 0.19 / 0.95 | 0.996 / 1.0 | data volume (17 attacks) |
| LinuxArena 217, cutoffs 7/3 | 0.040 / 0.115 | 0.12 / 0.39 | 0.97 / ≈1 | statistical margin (N ≤ 10); protocol (N = 100) |
| LinuxArena split, cutoffs 10/8, Opus | 0.74 / 0.82 | 0.93 / 0.98 | 0.93 / 0.996 | the monitor |
| LinuxArena split, Sol attacker | 0.94 / 0.98 | 0.99 / ≈1 | 0.99 / ≈1 | the monitor |
| LASR closed APPS (15) | 0.055–0.117 / 0.130–0.220 | 0.13–0.26 / 0.33–0.51 | 0.14–0.26 / 0.63–0.80 | statistical margin |
| LASR closed BigCodeBench (12) | 0.000–0.011 / 0.052–0.083 | 0.00–0.03 / 0.09–0.22 | 0.00–0.03 / 0.71–0.83 | statistical margin |
| LASR open APPS (15) | 0.005–0.22 / 0.06–0.43 | 0.01–0.30 / 0.10–0.60 | 0.25–0.97 / 0.99–1.0 | monitor and margin |

## Why the margin dominates at long horizons
Over 100 rounds the certificate is driven by the guaranteed LOWER bound on defer recall: each round a bad submission
escapes deferral with probability ≤ 1 − TPR_defer_lower, and a full-information Red compounds that. Example
(closed/BigCodeBench/acausal/none_base, 183/183 attacks deferred, 0/345 honest audited at ≥ 7):

| correction | defer-TPR lower | certified risk N=1 / 10 / 100 |
|---|---|---|
| preregistered: α = 1/20 over 42 conditions × 12 cutoffs × 2 rates × 2 tails | 0.9437 | 0.056 / 0.095 / 0.718 |
| one predeclared condition, 12 cutoffs | 0.9632 | 0.037 / 0.060 / 0.447 |
| one condition, only the 2 cutoffs used | 0.9726 | 0.027 / 0.044 / 0.284 |
| same, 80% confidence | 0.9800 | 0.020 / 0.031 / 0.162 |

Point estimate: 0.000 at every horizon.

## Consequences
- Tighter simultaneous ROC bands (e.g. `rocci`) would not change this much: at a fixed cutoff with zero misses, the
  Clopper–Pearson lower bound is already near-optimal. What matters: (1) predeclare only the operating points actually
  used (K = 2, not 12); (2) predeclare one condition instead of correcting across 42; (3) attack sample size: with zero
  misses the lower bound is ≈ 1 − 3/n at 95% (rule of three), so a 100-task bound of ≈ 0.1 needs on the order of
  1,000–3,000 attack samples, or fewer rounds/more audits.
- For weak monitors (LinuxArena at low false-alarm budgets) the certificate is close to the point estimate: the
  monitor, not the method, is the limit.

## Fresh-data check (2026-10-07)
The official LASR release (`huggingface.co/datasets/jbostock/untrusted-monitoring-2026-paper`) contains the same 42
test-split conditions as our archive (plus open-source `causal_train`/`self_rec_train` training-split runs). There is
no unseen LASR condition on which to run a clean single-condition, K = 2 preregistration; the tighter numbers above
remain post hoc.
