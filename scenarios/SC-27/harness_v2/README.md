# SC-27 harness v2: anchored evidence chain (witness fix)

This is a defensive reference test on one Linux host. A writer appends evidence entries to a hash-chained log whose
storage it controls. An **independent** witness periodically recomputes each log's head from storage and records it
in its **own** log. It refuses, as a fork, any state that does not extend its previous anchor; that check goes beyond
the model, and the prereg says so. A verifier accepts a manifest only if its recomputed head equals a head the witness
anchored.

The runner plays the writer-side adversary, benignly and by script, by rewriting the writer's storage.

**v2.** Motivated by the Lean refinement finding `SC27Refinement.empty_truncation_silent`: the v1 witness returned
"empty" before comparing with its last anchor, so truncating an anchored log to empty raised no fork alarm (safety was
unaffected). v2 is a copy of v1 with one change in `witness.py` (empty storage after an anchor is a FORK) and two new
hypotheses: H5 (the fix) and H6 (a NEGATIVE_CONTROL that runs the frozen v1 `../harness/witness.py` read-only and
must stay silent). v1 and its run-1 receipt are frozen and unmodified; v2 supersedes nothing.

The preregistration is [`prereg/SC27-ANCHOR-v2.md`](../../../prereg/SC27-ANCHOR-v2.md) (`PREREG-SC27-ANCHOR-v2`).
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
| H5 | v2 witness: an anchored log truncated to empty (empty file, deleted file) | fork alarm with n = 0; the empty manifest is still rejected | `SC27Refinement.empty_truncation_silent` (model half), `concrete_alarm_iff` |
| H6 | **NEGATIVE_CONTROL**: the frozen v1 witness on the same trace | silent ("empty", no fork record); safety still holds | `SC27Refinement.empty_truncation_silent` (runtime half) |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-27/harness_v2/run_sc27.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-27/harness_v2/run_sc27.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc27v2-run-*` directory (mode 0700). That directory is removed at the end.
- **Evidence:** all "evidence" is synthetic text in the run's own files.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 35 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
