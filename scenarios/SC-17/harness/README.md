# SC-17 harness: drift reconcile and apply gate

This is a defensive reference test on one Linux host. An apply gate owns the desired grant set. A diff applies only
if a separate reviewer (not the author) approved exactly that diff, and the ceiling holds on the **resulting** state:
no subject may hold both read:secrets and exec:prod.

A cluster process serves the live grant set. The runner injects benign out-of-band grants at d = 2 per 50 ms tick,
and a reconciler reverts drift every W = 4 ticks. Drift is reverted, not prevented; the claim is the model's bound of
d·W grants, each living less than W ticks.

The preregistration is [`prereg/SC17-DRIFT-RECONCILE.md`](../../../prereg/SC17-DRIFT-RECONCILE.md)
(`PREREG-SC17-DRIFT-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC17Infra.lean` and `SC17Drift.lean`.

## Files

| file | role |
|---|---|
| `cluster.py` | The live grant set. Its open `oob.sock` takes out-of-band adds. Its trusted `ctl.sock` takes versioned `set_state` pushes; a push older than the last is refused. Every mutation is logged with the full live set after it. |
| `gate.py` | The apply gate. Proposals and amendments come from the author only; approvals come only from the registered reviewer pid and record the exact diff. Apply checks the exact diff and the ceiling on the resulting state, then pushes desired to the cluster. `--text-ceiling` is a control. |
| `reviewer.py` | The reviewer. It fetches the current diff, logs it (fsync) and approves exactly that diff. |
| `reconciler.py` | The reconciler. On an absolute schedule of W ticks, it pushes desired to live when they differ. |
| `reconcile.py` | Independent reconciliation. Drift count and lifetimes come from the cluster log at every instant. The apply audit uses the gate's and reviewer's logs. It also has mutation self-tests. |
| `run_sc17.py` | The injector, the sampler, the agent, the H1–H5 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | drift at d = 2 per tick for 3 s, reconciler every 4 ticks, applies during drift | out-of-band live grants ≤ d·W + TAU_N; each lifetime ≤ W·TICK + TAU_L | `drift_bounded`, `drift_lifetime`, `live_eq`, `no_drift_detection_breaks` (deployed half) |
| H2 | two individually acceptable diffs that together give alice the forbidden pair | the second is refused | `sc17_safe`, `text_ceiling_composition_breaks` (deployed half) |
| H3 | approve, then amend | refused; the agent cannot approve its own diff; one apply after re-review | `approve_then_amend_breaks` (deployed half) |
| H4 | 20 honest applies | all succeed within L_APPLY; live = desired | `honest_apply` |
| H5 | **NEGATIVE_CONTROL**: (a) no reconciler; (b) text-only ceiling | (a) drift lifetime grows with run length; (b) the escalation applies and is flagged | `no_schedule_unbounded_lifetime`, `text_ceiling_composition_breaks` |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-17/harness/run_sc17.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-17/harness/run_sc17.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc17-run-*` directory (mode 0700). That directory is removed at the end.
- **Grants:** the "grants" are strings in the run's own JSON state; nothing touches real permissions.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 35 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
