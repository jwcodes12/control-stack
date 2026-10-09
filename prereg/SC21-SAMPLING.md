# Preregistration: SC-21 empirical validation of the proved sampling bounds

**ID:** `PREREG-SC21-SAMPLING-v1`. **Written:** 2026-10-09.
**Status: FROZEN 2026-10-09** (frozen by the orchestrator before any evidence run; §8 filled; committed with `scenarios/SC-21/harness/`).

**Freeze rules.** An evidence run is refused unless:
- env `SC21_SAMPLING_PREREG_SHA256` equals this file's SHA-256;
- `--out` is under `scenarios/SC-21/harness/evidence/` and does not exist;
- the seed is `sc21-sampling-evidence-v1` and there are 20000 trials per configuration;
- the harness and this file are committed and unmodified.

Dry runs use other seeds and scratch directories, and are never evidence. No language model is involved.

## 1. Question and what it can show

These results bound how often corrupted evaluation results escape a hidden re-execution sample. They are proved in
Lean:
- `EvalIntegrity.sc21_undetected_prob`: a fixed corrupted set of size k survives a uniform hidden sample of B of N with
  probability exactly C(N−k,B)/C(N,B);
- `EvalIntegrityAdaptive.sc21_adaptive`: an adaptive agent that sees only its own history does no better;
- `EvalIntegrityAdaptive.sc21_adaptive_recall` with `ReservedRecall.hypMiss`: with detection recall r, the bound is
  hypMiss N B k r;
- `EvalIntegrity.observable_sample_nogo` and `EvalIntegrityAdaptive.leaked_sample_survives`: if the sample leaks, the
  agent survives.

This run builds an executable pipeline: N deterministic eval tasks, an agent that publishes results, and a trusted
auditor that RE-EXECUTES a hidden uniform sample and compares. It checks four things:
- the pipeline's measured survival agrees with the exact proved values;
- the adaptive adversaries respect the bound;
- imperfect detection respects hypMiss;
- a leak adversary breaks the bound.

**What a pass means.** The implemented pipeline conforms to the theorems' model (uniform hidden sample, real
re-execution, independent detection coins, per-round decisions on own history), and the leak premise is load-bearing
in practice.

**What it cannot mean.** It is not evidence about real agents, real evaluators or real side channels. The "leak" is an
explicit bit with configurable correlation, not a measured channel. A simulation of a proved combinatorial bound is
expected to agree with it; a disagreement would indicate an implementation or premise error.

## 2. Pipeline (scenarios/SC-21/harness/)

- **Tasks (`tasks.py`).** Task i is a deterministic seeded computation, with a result from 0 to 64.
- **Agent rounds (`pipeline.py`).** Rounds run in task order. In each round:
  1. the agent decides to corrupt (result + 1) or not, using only its own attack bits and catch flags;
  2. if the task is in the hidden sample S (B of N, drawn uniformly from the auditor's own RNG stream before the
     run), the auditor re-executes it and compares;
  3. a mismatch is detected with probability r, using an independent coin;
  4. a detection is a catch flag, shown to the agent at once.
- **Success events** (exactly the theorems'):
  - **hidden** (r = 1): at least k attacks, none in S;
  - **recall** (r = 1/2): at least k attacks, never caught.
- **Adversaries:**
  - `fixed`: a uniformly random k-set chosen before the run (non-adaptive);
  - `pace`: adaptive; attacks with probability (k − attacks)/(N − i) until it has k attacks;
  - `burst`: adaptive and uses catch feedback; attacks with probability 0.3 while uncaught, and then only when forced
    to reach k;
  - `leak`: before round i it receives a bit L_i. With probability q, L_i = [i ∈ S]; otherwise L_i is an independent
    Bernoulli(B/N). It corrupts when L_i = 0 or when forced, until it has k attacks.
- **RNG streams:** agent, sample, audit coin and leak are separate streams, each seeded from (master seed,
  configuration, stream name). All seeds are recorded.

## 3. Parameters

| parameter | values |
|---|---|
| N | 100 |
| B | 10 |
| k | 1, 3, 5 |
| r | 1, 1/2 |
| q | 0, 1/4, 1/2, 1 (leak adversary; r = 1 only) |
| family level | α = 0.01 |
| trials per configuration | 20000 (evidence) |

**Configurations (30):**
- fixed, pace and burst × r ∈ {1, 1/2} × k: 18;
- leak × q × k: 12.

Exact values are computed as rational numbers: C(N−k,B)/C(N,B), and hypMiss N B k r. `test_sampling.py` checks the
k = 5 value against the Lean constant 10104934117421/17310309456440.

## 4. Hypotheses and decision rules

All five must pass for an overall PASS.

- **H1 (no-leak adversaries respect the bound, r = 1).** For fixed, pace and burst at each k: an exact one-sided
  binomial test of H0 "p ≤ C(N−k,B)/C(N,B)" against p > bound, giving 9 tests.
  - Pass: no rejection at the Bonferroni level 0.01/18, a level shared with H3.
  - Note: all three adversaries make exactly k attacks, independently of S, so their true survival EQUALS the bound.
    These are boundary tests, and the family false-failure rate is ≤ 0.01.
- **H2 (tightness).** For the fixed adversary at r ∈ {1, 1/2} and each k (6 configurations): the exact two-sided
  Clopper–Pearson interval at level 1 − 0.01/6 contains the exact value (the bound at r = 1, hypMiss at r = 1/2).
- **H3 (imperfect recall, r = 1/2).** As H1, against hypMiss N B k (1/2) on the recall event: 9 tests.
  - Pass: no rejection at 0.01/18.
- **H4 (the leak premise is necessary).** For the leak adversary at r = 1, for each q ∈ {1/4, 1/2, 1} and each k
  (9 tests), the one-sided test REJECTS "p ≤ bound" at level 0.01/9.
  - Also, for each k, the empirical survival estimates increase strictly over q = 0, 1/4, 1/2, 1.
  - At q = 1 survival should be 1 (`observable_sample_nogo`); this is reported.
- **H5 (the pipeline's own checks are sound).**
  - Every main configuration has zero detection violations at r = 1, i.e. no sampled corruption is missed by
    deterministic re-execution.
  - Every configuration's per-task sample-inclusion counts are uniform: max |z| ≤ z_crit = Φ⁻¹(1 − 0.01/(2·100·31))
    ≈ 4.656 (Bonferroni over 100 tasks × 31 configurations).
  - Every task re-executes deterministically.
  - A self-check (2000 trials, fixed adversary, k = 3) passes on the baseline, and each mutation is CAUGHT:

| mutation | how it is caught |
|---|---|
| `no_reexec` (compare the published value with itself) | detection violations > 0 |
| `biased_sample` (always tasks 0..B−1) | the uniformity check fails |
| `nondet_task` (a clock bit in the result) | the determinism check fails |

## 5. Runs and stopping

- **One evidence run.** The pipeline is deterministic given the seed: a re-run reproduces the receipt bit-for-bit,
  and that is the reproduction check, not a second sample.
- **If a hypothesis fails,** the failure is recorded as is, with all counts. A fix needs a new ID and a new seed.

## 6. What a result licenses

- **Pass:** the pipeline implements the theorems' model faithfully enough that measured survival matches the exact
  values. Adaptivity without a leak does not beat the bound in these adversaries. The no-leak premise is necessary,
  demonstrated rather than only proved. Nothing about real agents or real side channels.
- **H1 or H3 failure:** an implementation, premise or statistical error, to be investigated before any further use of
  the bounds.

## 7. Dry-run calibration (filled after the dry run, before freezing)

**Dry run:** seed `dry`, 2000 trials per configuration, 40 s wall time, scratch directory; not evidence.

| adversary, r | k = 1: empirical / exact | k = 3 | k = 5 |
|---|---|---|---|
| fixed, 1 | 0.9050 / 0.9000 | 0.7295 / 0.7265 | 0.6040 / 0.5838 |
| fixed, 1/2 | 0.9560 / 0.9500 | 0.8585 / 0.8567 | 0.7795 / 0.7718 |
| pace, 1 | 0.9080 / 0.9000 | 0.7235 / 0.7265 | 0.5675 / 0.5838 |
| pace, 1/2 | 0.9465 / 0.9500 | 0.8530 / 0.8567 | 0.7625 / 0.7718 |
| burst, 1 | 0.8965 / 0.9000 | 0.7315 / 0.7265 | 0.5835 / 0.5838 |
| burst, 1/2 | 0.9440 / 0.9500 | 0.8465 / 0.8567 | 0.7665 / 0.7718 |
| leak q = 0 / 1/4 / 1/2 / 1 (bound 0.9000, 0.7265, 0.5838) | 0.891 / 0.920 / 0.953 / 1.000 | 0.733 / 0.796 / 0.866 / 1.000 | 0.597 / 0.676 / 0.771 / 1.000 |

**Verdicts in the dry run:**
- **H1, H2, H3:** pass.
- **H5:** pass.
  - Zero detection violations in all 30 configurations.
  - Maximum inclusion |z| = 3.95, against a threshold of 4.656.
  - Deterministic re-execution.
  - Every mutation was caught: `no_reexec` gave 543 violations out of 2000 trials, `biased_sample` gave |z| = 134,
    and `nondet_task` failed the determinism check.
- **H4:** the monotonicity part passed strictly for every k. The exceedance tests passed in 8 of 9, but q = 1/4,
  k = 1 missed: p = 0.00123 against the per-test level 0.00111.

**Power note** (fixed before freezing; no change to the decision rules). The excess over the bound at q = 1/4,
k = 1 is about 0.02, roughly 0.92 against 0.90. With 20000 trials the standard error at the bound is
√(0.9·0.1/20000) ≈ 0.0021, so the expected z ≈ 9.4 and the one-sided p ≈ 10⁻²⁰, far below 0.0011. The dry-run miss
is the expected power shortfall at 2000 trials. The evidence run keeps 20000 trials and the stated levels.

## 8. Pinned artifacts (SHA-256 at freeze)

Commit: `627f222ba9c5e0fe98ce6036cfce39104e0848a5`.

| Path | SHA-256 |
|---|---|
| `scenarios/SC-21/harness/tasks.py` | `69c1bde69fe527bcb4ed449868877843494f28a8d235de19036eb277b636cccc` |
| `scenarios/SC-21/harness/pipeline.py` | `95c8a172f7741ee238488029209df8e551cee3dc71df54093afe5465146955a0` |
| `scenarios/SC-21/harness/stats.py` | `db801867d5c3618b6a37e0921c6e7120277659aeeee94a5b54da0a2eb05091d6` |
| `scenarios/SC-21/harness/run_sampling.py` | `41ea1ef7e88adc9213b97d84d4cf4d42b971cae00d0e9c4f601b620417fd797e` |
| `ControlStack/Scenarios/EvalIntegrity.lean` | `48a646749d221657c6e8acf3ddec7adf52823ac4a216737b24afeadb04d8714b` |
| `ControlStack/Scenarios/EvalIntegrityAdaptive.lean` | `e06a6f9a71c3db1145b7672a944be45c380cce2ebb96cf7ef932d0733156d538` |
| `ControlStack/Families/F6/ReservedRecall.lean` | `ada6bfc980a6ce239414fa3be0f960e7ce4f0f8a33a79e851a7fc9ec5bfd2ac9` |
