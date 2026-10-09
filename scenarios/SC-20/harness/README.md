# SC-20 harness: data provenance

This is a defensive reference test on one Linux host:
- **Sources:** allowlisted source processes register examples (digest and source, named by the kernel-reported
  pid).
- **Quarantine:** agent-written examples are quarantined.
- **Reviewer:** a separate process, never the writer, promotes exactly the current digest.
- **Freeze:** writes the training manifest.
- **Trainer:** a separate process running a trivial deterministic statistic. It consumes only frozen examples and
  re-checks every digest at read time.

**Nothing here says whether allowlisted or reviewed data is clean**: that is semantic and outside this test.

The preregistration is [`prereg/SC20-DATA-PROVENANCE.md`](../../../prereg/SC20-DATA-PROVENANCE.md)
(`PREREG-SC20-PROV-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC20Data.lean` and `AuthInstancesB.sc20_safe_authenticated`.

## Files

| file | role |
|---|---|
| `store.py` | The store, registry and freezer. Its sockets: ingest (sources, by pid), agent (quarantined writes), review (the registered reviewer pid only, never the writer), admin (freeze). Controls: `--no-quarantine`, `--no-source-check`. |
| `principal.py` | `--role source`, `reviewer` or `trainer`, each with its own fsync'd log. The trainer re-checks every digest at read time; `--no-recheck` is a control. |
| `reconcile.py` | Independent reconciliation over the trainer's consumed digests, the sources' and reviewer's own logs, and the trusted allowlist. It also has mutation self-tests. |
| `run_sc20.py` | The flows, the H1–H5 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | registered, promoted, unpromoted and self-promoted examples | exactly the registered and promoted ones are consumed; self-promotion refused | `sc20_safe`, `sc20_safe_authenticated`, `self_promotion_refused` |
| H2 | a label flipped after the freeze | the trainer refuses | `edit_after_freeze_breaks` (deployed half) |
| H3 | an unlisted source | excluded at freeze | `unlisted_source_breaks` (deployed half) |
| H4 | 220 examples | freeze and train within L_TRAIN | usefulness |
| H5 | **NEGATIVE_CONTROL**: no quarantine, no re-check, unlisted source accepted | consumed and flagged | the three `…_breaks` witnesses |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-20/harness/run_sc20.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-20/harness/run_sc20.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc20-run-*` directory (mode 0700). That directory is removed at the end.
- **Data:** all data is synthetic benign text.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 35 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
