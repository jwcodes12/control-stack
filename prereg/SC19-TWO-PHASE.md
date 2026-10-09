# Preregistration: SC-19 two-phase destructive operations, single-host reference run (v1)

**ID:** `PREREG-SC19-TWOPHASE-v1`. **Written:** 2026-10-09, before any dry run or evidence run.
**Freeze:** this file's Git commit and SHA-256 are recorded in every receipt. After the evidence run starts, this file
is not edited. A change needs a new ID (`-v2`), a new file and a new run. The earlier run is kept.

## 1. Claim under test and its scope

SC-19: no irreversible production damage without a fresh, verified restore point and an independent approval of a
bounded change. The mitigation tested here:
- **Production:** a disposable SQLite "production" DB of objects per target. Every write bumps the target's version
  and writes a history row in the same transaction.
- **Snapshot service:** copies the whole DB (SQLite online backup) and records each target's version, count and row
  hash from the copy.
- **Verifier:** a separate trusted process that restores each snapshot into its own scratch DB, runs an integrity
  check, and recomputes versions, counts and hashes before marking it verified.
- **Destructive operations** (delete all rows of a target) go through three steps:
  - **prepare:** records the op and its digest;
  - **approve:** a separate approver, never the author, approves the exact op digest;
  - **commit:** re-checks inside ONE `BEGIN IMMEDIATE` transaction, so no write can interleave. A verified snapshot
    must exist at the target's CURRENT version, and the affected count, recomputed at commit, must be ≤ R = 10.
- **A benign writer process** adds rows concurrently.

**Models (SHA-256 of both recorded in every receipt):**
- `ControlStack/Scenarios/SC19Prod.lean`;
- `ControlStack/Scenarios/AuthInstancesA.lean` (`sc19_safe_authenticated`).

**Implementation:** `scenarios/SC-19/harness/`:
- `dbutil.py`: schema and helpers;
- `writer.py`: the benign concurrent writer;
- `snapshot.py`: the snapshot service;
- `verifier.py`: restore and verify;
- `gate.py`: prepare / approve / commit;
- `approver.py`: the approver;
- `reconcile.py`: independent reconciliation and the restore drill;
- `run_sc19.py`: the checks and the receipt.

**Correspondence with the model.**

| model (`SC19Prod.lean`) | this run |
|---|---|
| `write t n` (version + 1, size + n) | writer: inserts n rows in one IMMEDIATE transaction, bumps `versions[t]`, appends a history row |
| `snapshot t` (records version and size) | whole-DB backup; per-target {ver, count, hash} read from the copy |
| `verify c i` (verifiers only) | the verifier restores the copy into a scratch DB, runs `integrity_check`, recomputes and compares; logs the verified record |
| `prepare c id t` (count at prepare) | gate `prepare`: op {id, target, kind, author}, digest = SHA-256 of it, count now |
| `approve c id` (approver ≠ author) | the approver fetches the pending op from the gate and approves exactly its digest. The gate's approver socket accepts only the registered approver pid (SO_PEERCRED); author = `agent:<pid>` |
| `commit id i` with `fresh`, `verified`, `atomicCount` | one IMMEDIATE transaction: approval of the exact digest by a non-author; verified snapshot; snapshot version of t = current version; count recomputed ≤ R; delete, bump the version, history row |
| `Destroy` (version destroyed, actual count, snapshot) | the gate's fsync'd record and the DB's own history row `destroy:<id>` |
| flags `fresh`, `verified`, `atomicCount` off | `--stale-ok`, `--unverified-ok`, `--prepare-count` (H6) |
| premise "a verified snapshot can in fact be restored" | tested by H4 (restore drill) |
| `halt` | the gate implements an admin halt, but no hypothesis exercises it |

**Not tested here, and not claimed:**
- **Adversarial agents.** Nothing bypasses the gate to write or delete directly, forges approvals, or tampers with
  snapshots. All processes share one UID, so credential separation and "destructive effects only through commit" are
  premises.
- **Downstream effects, restore speed, other kinds of destructive operations.**

## 2. Environment and trust

- **Host:** the OCI ARM64 Linux box running this repository (single host, shared with other work). No root: the runner
  refuses to run as root.
- **Interpreter:** the system Python (`/bin/python3`, 3.9) with its `sqlite3` (the SQLite version is recorded). Every
  child runs with `-I -S -B`.
- **Processes:** per stack, the snapshot service, verifier, approver, writer and gate, all children of the runner.
  Unix sockets only (mode 0600), and the DB and snapshot files, all in a fresh `/var/tmp/sc19-run-*` directory (mode
  0700). No TCP.
- **Receipt contents:**
  - the commit, dirty status, and the SHA-256 of the harness, of this file and of both Lean files;
  - the calibration;
  - per stack:
    - the gate, verifier, approver, snapshot and writer logs;
    - the gate's dump of deleted rows;
    - the DB's full history table;
    - every client call;
  - every check.

**Host-safety bounds** (part of this registration):
- every child exits by itself after 30 s, and the run has a 115 s wall limit;
- children are killed in `finally` blocks;
- after each repetition, an independent `/proc` scan for the work directory must be empty, or the run aborts;
- the work directory (DBs, snapshots) is removed at the end;
- the "production" DB is a disposable file created by the run.

## 3. Hypotheses and decision rules

**The reconciliation rule (`reconcile.py`).** For every committed destructive op:
- the DB's own history has exactly one `destroy:<id>` row; it gives the destroyed version (`ver_after − 1`), the rows
  removed and their hash;
- the verifier's own log has a VERIFIED record of the op's snapshot, committed before the op, whose recorded version
  AND row hash for the target equal the destroyed version and the destroyed rows' hash (the restore point holds
  exactly what was destroyed);
- the rows removed are ≤ R;
- the approver's own log has a record of exactly the op's digest (recomputed from the op it saw), for the same author,
  committed before the op, by a principal other than the author;
- no op is destroyed twice.

The rule is checked in H1–H5.

**Pass rule:** each hypothesis runs **5 repetitions** on fresh processes. A hypothesis passes only if every check
passes in all 5. An exception fails the repetition. For H6 (flagged `NEGATIVE_CONTROL`), pass means all its
configurations **fired**.

### 3.0 Tolerance calibration (fixed before any evidence run)

- **L_OP** (s): the bound on one honest destructive change in H5: snapshot, verify, prepare, approve and commit.
  L_OP = max(0.25, 3 × M) rounded up to 0.05 s, where M is the largest single-change latency over all H5 repetitions
  of the calibration dry runs.

Calibration uses at least two complete dry runs (5 repetitions, all hypotheses) with the harness at its final state.
The value and the receipts it came from are written below, the status is set to FIXED, and the harness constant is set
to the same value before the freezing commit. The runner refuses an evidence run otherwise.

```
CALIBRATION-STATUS: FIXED
L_OP = 0.7
```

Calibration record (2026-10-09). Two complete dry runs (5 repetitions × H1–H6), harness at its final state:
`sc19-dry-cal1` and `sc19-dry-cal2` (session scratch directory; dry, not evidence). Both overall PASS.
- **H5.** Per-repetition p50 was 72–129 ms and max 96–221 ms, with 52–86 background writes. M = 0.2208 s, so
  L_OP = max(0.25, 3 × 0.2208 = 0.662 rounded up to 0.05) = **0.70 s**.
- **H4.** All drills were byte-exact.
- **H6.** All three controls fired in every repetition. The stale-snapshot drill restores 4 of the 6 deleted rows:
  the writes after the snapshot are unrecoverable, which is the stale_snapshot_breaks outcome.
- Not used for calibration: the debugging run `sc19-dry0` (1 rep, PASS).

### H1 Every destructive commit is backed (`sc19_safe`, `sc19_safe_authenticated`, `honest_destructive_change`)

Six targets with 3–8 rows; each goes through snapshot, verify, prepare, approve and commit. Four refusals are also
tried, and each must give the stated reason:
- a target of 15 rows (> R): "affected 15 > R = 10";
- a commit with no approval: "no approval of exactly this operation by another principal";
- a commit naming an unverified snapshot: "snapshot not verified";
- the agent approving its own op on the approver socket: "not the approver", after which the commit is still refused
  for lack of approval.

- **Pass:** all of
  - the 6 honest ops commit;
  - the refusals give exactly those reasons;
  - only the 6 appear as destroys;
  - the reconciliation rule holds.
- **Sensitivity:** on copies of the stored evidence, each of these is flagged:
  - the verification dropped;
  - the destroyed version made newer than the snapshot;
  - the affected count set above R;
  - the approval dropped;
  - an approval of a different op.

### H2 Write after snapshot (deployed half of `stale_snapshot_breaks`)

3 targets of 4 rows each, each taken through snapshot, verify, prepare and approve. Then the writer adds 2 rows, and
the commit names the earlier snapshot.
- **Pass:** all of
  - every such commit is refused with "snapshot is not at the current version";
  - after a fresh, verified snapshot the same op commits and destroys all 6 rows;
  - the reconciliation rule holds.

### H3 Concurrent growth beyond R (deployed half of `blast_radius_race_breaks`)

3 targets of 8 rows. Each is prepared (count 8); the writer then adds 5 rows (13 > R); then snapshot, verify,
approve, commit.
- **Pass:** every commit is refused with "affected 13 > R = 10", nothing is destroyed, and the reconciliation rule
  holds.

### H4 Restore drill (the premise "a verified snapshot can in fact be restored")

3 targets of 5–7 rows go through the honest flow. Then, for each, the rows of the target in the verified snapshot
file are compared with the gate's dump of the rows it deleted.
- **Pass:** every op committed, and the restored rows equal the deleted rows byte-exactly, same ids and same payload
  bytes; the reconciliation rule holds.

### H5 Usefulness

20 targets of 5 rows go through the honest flow while the background writer adds a row to one of 4 other targets
every 20 ms.
- **Pass:** all 20 commit, each within L_OP; background writes happened; the reconciliation rule holds.
- Reported: latency p50 / max.

### H6 Controls (NEGATIVE_CONTROL)

Each configuration runs on a fresh stack with 2 ops. It **fires** iff both commit and the reconciliation flags
exactly those 2.

| | gate flag | trace | Lean witness |
|---|---|---|---|
| H6a | `--stale-ok` | snapshot, verify, write 2 rows, prepare, approve, commit with the old snapshot | `stale_snapshot_breaks` (a restore drill of the stale snapshot is reported: it lacks the rows written after it) |
| H6b | `--unverified-ok` | snapshot (no verify), prepare, approve, commit | `unverified_snapshot_breaks` |
| H6c | `--prepare-count` | prepare at 8 rows, write 5, snapshot, verify, approve, commit (13 rows removed) | `blast_radius_race_breaks` |

H6 passes only if all three fire.

**Overall pass:** H1–H6 all pass, the run is not aborted, and no process of the run survives.

## 4. Runs, re-runs and stopping

- **Dry runs** use `--kind dry`, write to scratch directories, and are not evidence. They are used for debugging and
  calibration.
- **The evidence run** is exactly one invocation of:
  ```
  /bin/python3 -B scenarios/SC-19/harness/run_sc19.py --kind evidence --reps 5 --out <new dir>
  ```
  - It runs from a commit in which this file and every harness file are committed and unmodified, with
    `CALIBRATION-STATUS: FIXED` and matching values. The runner refuses otherwise.
  - The receipt is kept whatever the outcome.
- **Infrastructure errors:** a re-run is allowed only for a preflight failure before any hypothesis starts. At most one
  re-run; both receipts are kept.
- **Failures are final:** they are never re-run under this ID.
- **Stop:** the runner aborts, with cleanup, if a process survives a repetition or the 115 s wall limit is reached.

## 5. What a pass licenses

On this host, this gate committed destructive operations only when:
- a separately verified snapshot held exactly the version and rows destroyed;
- the change, counted inside the committing transaction, was within R;
- a principal other than the author approved its exact digest.

It also refused stale snapshots and growth-after-prepare; the verified snapshots restored deleted rows byte-exactly;
and it stayed useful under concurrent writes. The reconciliation detects the three weakened configurations the model
predicts are unsafe. This is an operational premise for the SC-19 restore-point and blast-radius gate for this
implementation. It is not evidence about adversarial agents, other destructive paths, or production databases.

## 6. Mapping to the Lean models

| hypothesis | theorem(s) | role |
|---|---|---|
| H1 | `SC19.sc19_safe`, `AuthInstances.sc19_safe_authenticated`, `honest_destructive_change` | conclusion checked |
| H2 | deployed half of `stale_snapshot_breaks` (the `fresh` check) | conclusion checked |
| H3 | deployed half of `blast_radius_race_breaks` (the `atomicCount` check) | conclusion checked |
| H4 | premise "a verified snapshot can in fact be restored" | premise checked |
| H5 | none (usefulness) | usefulness |
| H6a–c | `stale_snapshot_breaks`, `unverified_snapshot_breaks`, `blast_radius_race_breaks` | necessity witnesses reproduced (negative controls) |

`halt_freezes` / `no_halt_check_breaks` are not exercised.
