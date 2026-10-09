# SC-27 harness: anchored evidence chain

This is a defensive reference test on one Linux host. A writer appends evidence entries to a hash-chained log whose
storage it controls. An **independent** witness periodically recomputes each log's head from storage and records it
in its **own** log. It refuses, as a fork, any state that does not extend its previous anchor; that check goes beyond
the model, and the prereg says so. A verifier accepts a manifest only if its recomputed head equals a head the witness
anchored.

The runner plays the writer-side adversary, benignly and by script, by rewriting the writer's storage.

The preregistration is [`prereg/SC27-ANCHOR-CHAIN.md`](../../../prereg/SC27-ANCHOR-CHAIN.md) (`PREREG-SC27-ANCHOR-v1`).
It holds the decision rules, the calibration, the re-run policy and the mapping to `SC27Chain.lean`.

## Files

| file | role |
|---|---|
| `chain.py` | The SHA-256 hash chain and the storage format, including the atomic rewrite the adversary uses. |
| `writer.py` | Appends entries (fsync). `publish_head` records heads the writer vouches for itself (control H4b). |
| `witness.py` | The independent witness. It works periodically (`--period`) and on request, recomputes heads from storage, keeps its own log (fsync), and raises a fork alarm on non-extensions. |
| `verifier.py` | Accepts a manifest iff its head was anchored by the witness for that log. Controls: `--current-head`, `--writer-heads`. |
| `reconcile.py` | Compares accepted manifests with the witness's own log, with mutation self-tests. |
| `run_sc27.py` | The tamper scripts, the H1–H4 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | after anchoring: modify, reorder, truncate, unanchored suffix, full recomputed rewrite | all rejected; the witness raises a fork alarm instead of anchoring the tampered states | `sc27_safe`, `tamper_after_anchor_detected`, `unanchored_suffix_breaks` (deployed half) |
| H2 | honest appends with a periodic witness (P = 0.25 s) | accepted within P + TAU_A | `honest_accept` |
| H3 | rewrite after a delay of 0 to 1.5P | accepted exactly when no state of the log was anchored before the rewrite; window ≤ P + TAU_W | `rewrite_before_anchor_window` (honest limit) |
| H4 | **NEGATIVE_CONTROL**: verifier trusts the current storage head, or the writer's own heads | the fabricated log is accepted and flagged against the witness log | `no_anchor_rollback_breaks`, `self_signed_breaks` |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-27/harness/run_sc27.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-27/harness/run_sc27.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc27-run-*` directory (mode 0700). That directory is removed at the end.
- **Evidence:** all "evidence" is synthetic text in the run's own files.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 35 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
