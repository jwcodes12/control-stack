# SC-22 harness: replication sampling

This is a small companion of the SC-21 sampling validation. A scripted reporter process reports N = 100 findings per
trial and misreports k of them, choosing which without seeing the sample.

A separate replicator process does three things, in order:
1. It **commits** to the reports.
2. It **draws** a hidden uniform sample of B = 10 findings, with its own seed.
3. It **re-runs** a deterministic toy experiment on the sampled findings and flags mismatches.

The undetected fraction is compared with the exact C(N−k, B)/C(N, B) using an exact Clopper–Pearson interval. In the
control, the sample is visible to the reporter in advance.

Replication checks numerical reproducibility only. **Whether a finding is correctly interpreted is semantic and
outside this test.**

The preregistration is [`prereg/SC22-REPLICATION.md`](../../../prereg/SC22-REPLICATION.md) (`PREREG-SC22-REPL-v1`). It
holds the decision rules, the fixed trial count, the re-run policy and the mapping to `EvalIntegrity.lean`.

## Files

| file | role |
|---|---|
| `reporter.py` | The scripted reporter. Its misreport choice is non-adaptive, or avoids the sample in the visible control. It logs the misreported set per trial. |
| `replicator.py` | The replicator: commitment, hidden post-commitment sample, re-run, flags. It also handles `draw`, which pre-draws samples for the visible control. |
| `analyse.py` | Structural checks (verdict = sample ∩ misreported ≠ ∅; sample drawn after the commitment), the exact interval, sample uniformity and mutation self-tests. |
| `stats.py` | Copied byte-for-byte from `scenarios/SC-21/harness/stats.py` (SHA-256 `db801867…91d6`): the exact bound and Clopper–Pearson. |
| `run_sc22.py` | The runner and the receipt. Evidence runs use the preregistered seed. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | hidden sample, k = 1, 3, 5 | the exact value lies in the exact CI; verdicts structurally correct; uniform samples | `sc22_unreplicated_misreport`, `sc21_example` |
| H2 | k = 0 | never flagged | `undetected_iff_disjoint` |
| H3 | **NEGATIVE_CONTROL**: visible sample | misreports always survive | `observable_sample_nogo` |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-22/harness/run_sc22.py --kind dry --reps 5 --out /path/to/new-dir [--seed S]

# the single evidence run (preregistered seed; committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-22/harness/run_sc22.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc22-run-*` directory (mode 0700). That directory is removed at the end.
- **Workload:** arithmetic on synthetic numbers.
- **Self-exit and wall limit:** children exit by themselves after 60 s, and the run has a 115 s limit. A full run
  takes about 30 s.
