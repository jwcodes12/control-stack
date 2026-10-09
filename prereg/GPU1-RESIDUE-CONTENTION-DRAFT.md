# Preregistration DRAFT: GPU-1, single-GPU memory residue and time-slicing contention channel

**ID:** `PREREG-GPU1-v1` (assign at freeze). **Drafted:** 2026-10-09.
**Status: DRAFT. Not frozen, not citable, not runnable here.**

**Requires owner approval and resources the project does not have:**
- one NVIDIA GPU host with root, where the driver, MPS and (if available) MIG configuration may be changed;
- an A100/H100-class part for the MIG arm;
- written owner approval of the host, the workloads and the data retention.

The workloads are benign: canary patterns and timing loops. No other tenant's data may be read. The host must be
dedicated to this run.

**Freeze:**
1. Write the harness (`experiments/gpu1/`, path to be fixed), using the `tools/new_scenario.py` conventions: the
   evidence label is refused unless this prereg is frozen, its SHA-256 is in env `GPU1_PREREG_SHA256`, the output is
   under the evidence directory, the §7 pins match, and the pinned files are committed.
2. Rename this file to a final name, fill §7 and commit everything before the evidence run.

## Review lessons checklist (from reviews/sc26-2026-10-09/opus-review-summary.md; tick before freezing)

- [ ] **Pin hashes in the prereg** (§7) after committing the harness and analysis code.
- [ ] **Controls must fire their specific finding:**
  - the positive control (H3a) must show the channel;
  - the negative control (H3b) must not.
- [ ] **Every analysis rule can fire:** a synthetic data mutation makes each decision rule flip.
- [ ] **Dev runs are labelled dry** and go to scratch; exactly one evidence run per arm.
- [ ] **Bin edges and sample sizes are fixed** from a calibration phase on separate data, before the evidence run.
- [ ] **Report negative results.** A canary found or a large Σ is a result. It is never a reason to re-run.
- [ ] **Novelty:** none claimed. GPU residue (e.g. LeftoverLocals, 2024) and contention channels are known classes.

## 1. Claim under test and its scope

The run instantiates the parameters of `ControlStack/Families/F2/ChannelInstances.lean` for one GPU. It measures, it
does not assume:
- `gpu_bound`: recovery ≤ (Σ_o max_s W s o)^m / |M|;
- `gpu_partition`: Σ = 1 when the receiver's view does not depend on the sender;
- `gpu_jitter`: Σ ≤ 1 + δ.

It also tests the premise `memory_scrub_between_tenants` of the `gpu_multitenancy` component in
`stack/components.json`.

**Premises the run tests but cannot prove:**
- stationarity of W over the run;
- one sender bit per quantum;
- that the measured isolation mode is the one configured.

**Not tested and not claimed:**
- memory-bandwidth, L2, NVLink, power, thermal and clock channels, which need their own certificates;
- multi-level occupancy;
- other GPU models, drivers or firmware;
- any production scheduler.

## 2. Environment

- **Host and record:** one GPU host, recording `nvidia-smi -q`, the driver/CUDA versions, the MIG and MPS state,
  `uname -a`, and the CPU governor.
- **Principals:** two numeric UIDs, SENDER and RECEIVER, in separate processes, plus the CONTROLLER (root).
- **Arms:**
  - **T:** time-slicing (default context switching);
  - **P:** MPS;
  - **M:** MIG with two instances; skipped and recorded as NOT-RUN if the part lacks MIG.
- **Receipt contents:** commit, dirty status, artifact hashes, every seed, the raw per-trial timings, and residue scan
  dumps (offsets and counts only, never raw memory beyond the canary match).

## 3. Hypotheses and decision rules

**H1 Residue.**
- **Procedure:** in each arm and each of 3 memory classes (global allocation, shared memory, local/stack memory in a
  kernel), SENDER writes a 64-byte canary pattern across its buffer and exits, with no explicit clear. RECEIVER then
  allocates the same size and scans.
- **Decision:** with N = 200 trials per arm and class, the premise is REFUTED for that arm and class if any canary
  match is found, and NOT REFUTED otherwise. The Clopper–Pearson upper bound on the per-trial leak rate is reported
  at 95%.

**H2 Contention channel.**
- **Calibration:** run on separate seeds. It fixes the receiver kernel, J = 4 bins by quantiles of the idle
  distribution, and the quantum length.
- **Evidence phase:** per arm, n = 5000 quanta, with the sender's bit s drawn by CONTROLLER from a seeded generator
  that the sender reads but the receiver never sees. The receiver records its quantised completion time.
- **Estimate:** Ŵ(s, o) per cell, with simultaneous one-sided 95% Clopper–Pearson upper bounds U(s, o) (Bonferroni
  over the 2·J cells). The reported certificate is Σ_U = Σ_o max_s min(1, U(s, o)), which is conservative.
- **Report:**
  - Σ_U;
  - the bits per quantum, log₂ Σ_U;
  - the `gpu_bound` value for m = 10 quanta and a 16-bit secret.
- **Arm M:** if the MIG arm's Σ_U ≤ 1.02, record it as consistent with `gpu_partition`.

**H3 Controls.**
- **(a) Positive.** Sender and receiver share one process and context with maximal contention. The control passes
  only if the lower confidence bound on Σ exceeds 1. This shows the instrument can see a channel.
- **(b) Negative.** The sender is absent (always idle). The control passes only if Σ_U ≤ 1 + the calibration
  tolerance.
- **(c) Analysis sensitivity.** Replacing the evidence data with a synthetic W of known Σ (for example the
  `gpu_example` matrix, Σ = 1.4) must recover Σ within tolerance.

All three must pass for any H2 number to be reported as a certificate.

## 4. Runs, re-runs and stopping

- Dev runs are labelled `dry`. There is one evidence run per arm.
- An infrastructure error before the first trial (driver reset, MIG reconfiguration failure) allows one further run;
  both are kept.
- **Stop** on any process outside the two UIDs touching the GPU, on any ECC or Xid error, or on thermal throttling
  recorded during a phase (that phase is marked INVALID).

## 5. What a pass licenses

A pass licenses measured values of Σ and the residue rate for this GPU, driver and configuration. Those values can be
plugged into `gpu_bound` as a CONDITIONAL certificate for the stated channel only. It is not a statement about other
channels or hosts.

## 6. What a fail means

- A residue match REFUTES the scrub premise for that arm.
- A control failure invalidates the H2 numbers.

Both are recorded with their raw data. A redesign needs a new ID.

## 7. Pinned artifacts (SHA-256 at freeze)

Harness commit: `PENDING`. An evidence label is refused while any row is `PENDING`.

| Path | SHA-256 |
|---|---|
| `ControlStack/Families/F2/ChannelInstances.lean` | `PENDING` |
| `experiments/gpu1/residue.cu` (to be written) | `PENDING` |
| `experiments/gpu1/contention.cu` (to be written) | `PENDING` |
| `experiments/gpu1/run_gpu1.py` (to be written) | `PENDING` |
| `experiments/gpu1/analyse.py` (to be written) | `PENDING` |
