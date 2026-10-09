# DC-1 single-host rehearsal: fencing sink vs. HALT delivery

This is a defensive reference test on one Linux host. It rehearses DC-1 (`prereg/DC1-DISTRIBUTED-HALT-DRAFT.md`,
STACK-MAP §4 item 4) and does not replace it. Eight benign worker processes send small JSON effects at a fixed rate to
one effect sink. A controller issues HALT, delays its delivery to each worker, and bumps the sink's epoch so that
effects stamped with the old epoch are rejected. All landing times come from the sink's own clock.

The preregistration is [`prereg/DC1-REHEARSAL-SINGLEHOST.md`](../../../prereg/DC1-REHEARSAL-SINGLEHOST.md)
(`PREREG-DC1R-SINGLEHOST-v1`). It holds the decision rules, the tolerance calibration, the re-run policy and the
mapping to `ControlStack/Families/F3/DistributedHalt.lean`.

This lives under `experiments/` rather than `scenarios/` because it is not an SC-xx scenario. `tools/check_scenarios.py`
accepts only SC-xx folder names under `scenarios/`.

## Files

| file | role |
|---|---|
| `sink.py` | The effect sink. It is single-threaded and appends to a JSONL log. Each effect is stamped with the sink's CLOCK_MONOTONIC when it is processed, and accepted iff fencing is off or the effect's epoch ≥ the sink's current epoch. Control commands are MARK (t0), BUMP (the fence) and STOP (drain the sockets, then fsync the log). |
| `worker.py` | A benign worker. It emits effects at most every 1/ρ seconds and never bursts to catch up. It stops for good on `HALT` read from stdin. `EPOCH n` changes the epoch it holds; only the H4 control uses this. |
| `analyse.py` | Measurements and decision rules over a stored sink log: t0, tF, ε̂, L̂, δ̂ᵢ, A_t0, A_tF, and the bounds N·ρ·(L̂+Δ̂) and N·ρ·(L̂+ε̂). It also has mutation self-tests showing that each rule can fire. It can be run on its own: `python3 analyse.py <sink.log>`. |
| `run_dc1r.py` | The controller and runner. It runs H1–H4 × reps on fresh processes, scans `/proc` independently for leftover processes, and writes the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | unfenced, all 8 workers get HALT at t0 + δᵢ (δᵢ ≤ Δ = 0.2 s) | accepted after t0 ≤ N·ρ·(L̂+Δ̂) + TAU_A | `landed_after_le` |
| H2 | fenced, worker 7 never gets HALT | 0 accepted at or after tF = t0 + ε̂; ≤ N·ρ·(L̂+ε̂) + TAU_A after t0 | `fenced_after_eps`, `partition_fenced`, `fenced_window` |
| H3 | **NEGATIVE_CONTROL**: unfenced, worker 7 never gets HALT | worker 7's accepted landings after t0 keep growing at ≈ ρ and exceed the bounded-delivery bound | `partition_unbounded` |
| H4 | **NEGATIVE_CONTROL**: fenced, worker 7 partitioned and handed the new epoch | ≥ 1 accepted landing from worker 7 after tF, none from any other worker | `token_leak` |

## Run

No root is needed, and the runner refuses to run as root. Use the system Python 3.9.

```
# dry run (debugging and calibration, not evidence); --only H1,H3 and --reps N are allowed
/bin/python3 -B experiments/DC-1-rehearsal/harness/run_dc1r.py --kind dry --reps 5 --out /path/to/new-dir

# the single preregistered evidence run
#   needs: committed, unmodified harness and prereg, and CALIBRATION-STATUS: FIXED in the prereg
/bin/python3 -B experiments/DC-1-rehearsal/harness/run_dc1r.py --kind evidence --reps 5 --out /path/to/new-dir
```

The runner refuses an `--out` that already exists. The receipt holds:
- `meta.json`: commit, dirty status, SHA-256 of the harness, the prereg and the Lean model, calibration status,
  `uname`, Python version, load averages and constants;
- `results.jsonl`: one line per hypothesis × repetition, with checks as expected / observed / pass, all
  measurements, and the controller timeline;
- `verdicts.json`, with controls flagged `negative_control`;
- `cleanup.json`;
- `summary.md`;
- `logs/`: each repetition's full sink log (gzip), worker reports and stderr.

The exit status is 0 only for an overall PASS. For the controls, PASS means the control fired.

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix stream sockets (mode
  0600) are used, in a fresh `/var/tmp/dc1r-run-*` directory (mode 0700). That directory is removed at the end.
- **Load:** one sink and 8 workers per repetition, sending about 400 small messages per second in total.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the whole run has a 115 s limit
  (SIGALRM). A full 5-rep run takes about a minute.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan for the
  work directory must find nothing, or the run aborts. At the end, anything left is SIGKILLed.
