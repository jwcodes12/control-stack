# Preregistration: SC-22 replication sampling, single-host reference run (v1)

**ID:** `PREREG-SC22-REPL-v1`. **Written:** 2026-10-09, before any dry run or evidence run.
**Freeze:** this file's Git commit and SHA-256 are recorded in every receipt. After the evidence run starts, this file
is not edited. A change needs a new ID (`-v2`), a new file and a new run. The earlier run is kept.

## 1. Claim under test and its scope

SC-22: misreported research findings. The formal statement (`ControlStack/Scenarios/EvalIntegrity.lean`,
`sc22_unreplicated_misreport`) is a sampling bound. Misreporting k of N findings survives independent replication of
a uniformly random **hidden** sample of B of them with probability exactly C(N−k, B)/C(N, B). The adversary is
NON_ADAPTIVE: it fixes the misreported set without seeing the sample. If the sample is observable in advance, the
reporter survives with probability 1 (`observable_sample_nogo`).

This run is a small companion of the SC-21 sampling validation (`prereg/SC21-SAMPLING.md`). It checks that a real
two-process replication protocol behaves as the bound says:
- **The reporter** reports N = 100 findings per trial and misreports k of them (value + 1). It chooses which with
  its own RNG, without seeing the sample.
- **The replicator** is a separate process. It commits to the reports (SHA-256), then draws a hidden uniform sample of
  B = 10 with a seed the reporter never receives, re-runs the toy experiment on the sampled findings and flags
  mismatches.
- **The control:** the replicator draws the samples first and the reporter is shown them.

Replication here checks numerical reproducibility of a deterministic toy experiment. **Whether a reproducible finding
is correctly interpreted is semantic and outside this test.**

**Implementation:** `scenarios/SC-22/harness/`:
- `reporter.py`;
- `replicator.py`;
- `analyse.py`: structural checks, the exact interval, uniformity and mutation self-tests;
- `stats.py`: copied byte-for-byte from `scenarios/SC-21/harness/stats.py`
  (SHA-256 `db801867d5c3618b6a37e0921c6e7120277659aeeee94a5b54da0a2eb05091d6`; exact bound, Clopper–Pearson);
- `run_sc22.py`: the checks and the receipt.

**Correspondence with the model.**

| model (`EvalIntegrity.lean`) | this run |
|---|---|
| `rep`, `truth : Fin N → ℕ`; `corrupt` = {i : rep i ≠ truth i} | claims vs `experiment(t, i)`; the reporter logs its misreported set A per trial |
| deterministic re-execution: undetected ⇔ sample ∩ A = ∅ (`undetected_iff_disjoint`) | the replicator re-runs `experiment` on the sample and flags mismatches; the analysis checks verdict = (sample ∩ A ≠ ∅) and flags = sample ∩ A in every trial |
| `randomSchedules N B` (uniform hidden B-subset) | `random.Random(seed).sample(range(N), B)` in the replicator, drawn AFTER the commitment, seed never sent to the reporter; uniformity checked |
| `survival = C(N−k,B)/C(N,B)` | the observed undetected fraction vs the exact value (exact two-sided Clopper–Pearson) |
| `observable_sample_nogo` | H3: samples drawn and shown first; the reporter misreports only unsampled findings |

**Not tested here, and not claimed:**
- **Adaptive reporters.** Reporters that learn about the sample from feedback (the leakage machinery in
  `EvalIntegrityAdaptive` / `ReservedRecall`; SC-21 covers part of it).
- **Nondeterministic replication.**
- **Semantic truthfulness of findings.**
- **Adversarial attacks on the replicator's seed or process.** The seed's secrecy and the replicator's independence
  are premises: same UID, same host.

## 2. Environment and trust

- **Host:** the OCI ARM64 Linux box running this repository (single host, shared with other work). No root: the runner
  refuses to run as root.
- **Interpreter:** the system Python (`/bin/python3`, 3.9); every child runs with `-I -S -B`.
- **Processes:** per stack, one reporter and one replicator, children of the runner. Unix sockets only (mode 0600), in
  a fresh `/var/tmp/sc22-run-*` directory (mode 0700). No TCP.
- **Seeds:** the evidence seed is `sc22-replication-evidence-v1`. Per configuration and repetition, the reporter's
  and the replicator's seeds are derived from it with distinct labels; the reporter only ever receives its own.
- **Receipt contents:**
  - the commit, dirty status, and the SHA-256 of the harness, of this file and of `EvalIntegrity.lean`;
  - the seed;
  - per stack, both logs (gzip): per trial, the misreported set, the sample, the flags, the verdict, and the
    commitment and draw time stamps;
  - every test.

**Host-safety bounds** (part of this registration):
- every child exits by itself after 60 s, and the run has a 115 s wall limit;
- children are killed in `finally` blocks;
- after each repetition, an independent `/proc` scan for the work directory must be empty, or the run aborts;
- the work directory is removed at the end;
- the workload is arithmetic on synthetic numbers.

## 3. Hypotheses and decision rules

**Parameters:** N = 100, B = 10, k ∈ {1, 3, 5} (the exact values are 0.9, 0.72653…, 0.58375…; `sc21_example`).
TRIALS trials per configuration per repetition, with α = 0.01.

**Pass rule:** each hypothesis runs **5 repetitions** on fresh processes, with seeds that differ per repetition. A
hypothesis passes only if every check passes in all 5. An exception fails the repetition. For H3 (flagged
`NEGATIVE_CONTROL`), pass means the control **fired** in every repetition.

### 3.0 Fixed from dry-run timing (before any evidence run)

There is no timing tolerance: the decision rules are exact statistical tests at a preregistered α. The only value
fixed after the dry runs is TRIALS. Rule: the largest value in {1000, 2000, 4000} for which a complete dry run takes
at most 60 s, half the wall limit. The value and the receipts it came from are written below, the status is set to
FIXED, and the harness constant is set to the same value before the freezing commit. The runner refuses an evidence
run otherwise.

```
CALIBRATION-STATUS: FIXED
TRIALS = 2000
```

Calibration record (2026-10-09).
- **TRIALS = 2000:** `sc22-dry-cal1` and `sc22-dry-cal2` (5 repetitions each) both PASS, in 25 s and 14 s.
- **TRIALS = 4000:** `sc22-dry-cal3` and `sc22-dry-cal4` both PASS, in 26 s and 28 s, at a load average of 4–7.
  Every interval contained the exact value. The maximum |z| for uniformity was 2.07–3.32, against a bound of about
  4.06.
- **Confirmation run at 4000:** `sc22-dry-final` (PASS) took **71 s** at a load average of about 6. That is over
  the 60 s criterion, so 4000 does not satisfy the rule on every dry run.
- The rule is applied conservatively, to every dry run at a value: **TRIALS = 2000**. This also leaves a wide margin
  under the 115 s wall limit on this shared host.
- **Confirmation run at 2000:** `sc22-dry-final2` PASS, 46 s at a load average of about 7.
- Not used for calibration: the debugging runs `sc22-dry0` and `sc22-dry1`. `sc22-dry0` hit the wall limit:
  unbuffered socket reads of megabyte-sized messages, fixed by using buffered socket files.
- All runs are session-scratch dry runs, not evidence.

### H1 Hidden sample: the exact bound (`sc22_unreplicated_misreport`, `sc21_example`)

For each k ∈ {1, 3, 5}: TRIALS trials with a hidden sample.
- **Pass:** all of
  - for every k, the exact value C(N−k, B)/C(N, B) lies in the exact two-sided Clopper–Pearson interval of the
    observed undetected fraction, at level 1 − 0.01/15 (Bonferroni over 3 values of k × 5 repetitions);
  - **structural:** in every trial, the verdict equals (sample ∩ misreported ≠ ∅), the flags equal sample ∩
    misreported, and every hidden sample was drawn after the commitment;
  - **uniformity:** pooled over the three configurations, every finding's inclusion count is within the two-sided
    Bonferroni z bound at α = 0.01/5 over N findings.
- **Sensitivity:** on copies of the logs, a flipped verdict and a sample drawn before the commitment each make the
  structural check fail.

### H2 No false flags

k = 0, TRIALS trials with a hidden sample.
- **Pass:** no trial is flagged, and the structural check holds.

### H3 Control: visible sample (`observable_sample_nogo`)

For each k ∈ {1, 3, 5}, the replicator draws the samples first and the reporter is shown them; it misreports k
findings outside each sample.
- **Fires (pass) iff:** for every k, all TRIALS trials are undetected (survival exactly 1, against the hidden-sample
  value), and the structural check holds.

**Overall pass:** H1–H3 all pass, the run is not aborted, and no process of the run survives.

## 4. Runs, re-runs and stopping

- **Dry runs** use `--kind dry` (a random or given `--seed`), write to scratch directories, and are not evidence. They
  are used for debugging and for fixing TRIALS.
- **The evidence run** is exactly one invocation of:
  ```
  /bin/python3 -B scenarios/SC-22/harness/run_sc22.py --kind evidence --reps 5 --out <new dir>
  ```
  - It uses the preregistered seed and refuses `--seed`.
  - It runs from a commit in which this file and every harness file are committed and unmodified, with
    `CALIBRATION-STATUS: FIXED` and matching TRIALS. The runner refuses otherwise.
  - The receipt is kept whatever the outcome.
- **Infrastructure errors:** a re-run is allowed only for a preflight failure before any hypothesis starts. At most one
  re-run; both receipts are kept.
- **Failures are final:** they are never re-run under this ID. With 15 interval tests at a family level of 0.01, a
  chance failure is possible (probability at most 0.01), and it would stand.
- **Stop:** the runner aborts, with cleanup, if a process survives a repetition or the 115 s wall limit is reached.

## 5. What a pass licenses

On this host, a two-process replication protocol, in which the replicator commits to the reports and only then draws
a hidden sample with its own seed:
- detected misreports exactly when the sample met them;
- left k of 100 misreports undetected at the exact rate C(100−k, 10)/C(100, 10), within exact confidence intervals,
  for k = 1, 3, 5;
- never flagged honest reports.

When the sample was visible in advance, misreports always survived. This is an operational check of the SC-22
replication bound's premises (hidden, uniform, post-commitment sample; deterministic replication) for this
implementation. It is not evidence about adaptive reporters, nondeterministic replication, or whether findings are
correctly interpreted.

## 6. Mapping to the Lean model

| hypothesis | theorem(s) in `ControlStack.EvalIntegrity` | role |
|---|---|---|
| H1 | `sc22_unreplicated_misreport` (= `sc21_undetected_prob`), `undetected_iff_disjoint`, `sc21_example` | bound checked, with its premises (hidden, uniform, deterministic) |
| H2 | `undetected_iff_disjoint` with an empty corrupted set | non-vacuity / no false flags |
| H3 | `observable_sample_nogo` | necessity witness reproduced (negative control) |
