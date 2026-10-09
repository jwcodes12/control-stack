# SC-19 harness: two-phase destructive operations

This is a defensive reference test on one Linux host. A disposable SQLite "production" DB holds objects per target,
and every write bumps the target's version. A snapshot service copies the DB, and a separate trusted verifier restores
each copy into a scratch DB and checks it before marking it verified.

A destructive operation goes through three steps:
- **prepare:** records the operation and its digest;
- **approve:** a separate approver, never the author, approves the exact digest;
- **commit:** inside one `BEGIN IMMEDIATE` transaction, it re-checks that a verified snapshot exists at the
  target's **current** version and that the affected count, recomputed now, is at most R = 10.

A benign writer process adds rows concurrently.

The preregistration is [`prereg/SC19-TWO-PHASE.md`](../../../prereg/SC19-TWO-PHASE.md) (`PREREG-SC19-TWOPHASE-v1`). It
holds the decision rules, the calibration, the re-run policy and the mapping to `SC19Prod.lean` and
`AuthInstancesA.sc19_safe_authenticated`.

## Files

| file | role |
|---|---|
| `dbutil.py` | The schema (`objs`, `versions`, `history`) and the helpers for writes, hashes and per-target summaries. |
| `writer.py` | The benign concurrent writer: commanded writes plus an optional background stream. |
| `snapshot.py` | Whole-DB snapshots via the SQLite backup API, recording each target's version, count and hash from the copy. |
| `verifier.py` | Restores the snapshot into its own scratch DB, runs `integrity_check`, recomputes and compares, and logs the verified record (fsync). |
| `gate.py` | prepare / approve / commit. The approver socket accepts only the approver's pid (SO_PEERCRED). Controls: `--stale-ok`, `--unverified-ok`, `--prepare-count`. |
| `approver.py` | The approver. It fetches the exact pending operation, logs it (fsync) and approves exactly its digest. |
| `reconcile.py` | Independent reconciliation from the DB history and the verifier's and approver's own logs, plus the restore drill and mutation self-tests. |
| `run_sc19.py` | The flows, the H1–H6 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | 6 honest ops, plus four refusals: oversize, no approval, unverified snapshot, self-approval | each committed op had a verified restore point of exactly the destroyed version and rows, ≤ R rows, and a non-author approval | `sc19_safe`, `sc19_safe_authenticated` |
| H2 | a write after the snapshot | refused until a fresh snapshot is taken and verified | `stale_snapshot_breaks` (deployed half) |
| H3 | prepared at 8 rows, grown to 13 before commit | refused | `blast_radius_race_breaks` (deployed half) |
| H4 | restore drill | the snapshot restores the deleted rows byte-exactly | premise: verified snapshots restore |
| H5 | 20 honest ops while background writes run | all commit within L_OP | usefulness |
| H6 | **NEGATIVE_CONTROL**: stale snapshot, unverified snapshot, prepare-time count | commits, and every one is flagged | the three `…_breaks` witnesses |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-19/harness/run_sc19.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-19/harness/run_sc19.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used.
- **Files:** the DB and snapshot files live in a fresh `/var/tmp/sc19-run-*` directory (mode 0700), which is removed
  at the end. The "production" DB is a disposable file the run creates.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 35 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
