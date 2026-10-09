# Preregistration: anti-rollback (a gate bound to an external monotonic anchor)

**ID:** `PREREG-ANTI-ROLLBACK-v1`. **Written:** 2026-10-09, before any evidence run (after the dry runs in §7).
**Status: FROZEN 2026-10-09** (frozen by the orchestrator before any evidence run; §8 filled; committed with the harness).

**Freeze:**
1. Replace the status line with `Status: FROZEN <date>` and fill §8.
2. Commit this file together with `experiments/anti-rollback/harness/`.

The runner refuses `--kind evidence` while the status line above still says DRAFT.

## 1. Claim under test and scope

**Premise:** `anti_rollback` (ASSURANCE-LEDGER.md row 8: SC-14, SC-28; also the SC-26 nonce history). It says
ledgers, counters and nonce history cannot be rolled back. Until now it had no runtime evidence.

**Model:** `ControlStack/Core/AntiRollback.lean`. It was written in parallel and was uncommitted when this draft was
written; re-check the names at freeze.
- `rollback_transfer` and `accepts_only_fresh`: under the anchor, whatever is released is the plain run of the
  committed ops, for any interleaving of writes, commits, restarts and rollbacks to any backup.
- `crash_recovery_commits` and `crash_then_rollback_halts`: the crash window.
- `honest_liveness`.
- `nonce_replay_without_anchor` and `rollback_without_anchor_double_spends`: necessity.

**What the harness implements (`experiments/anti-rollback/harness/`).** Three processes, each with its own numeric
UID:

| process | UID | role |
|---|---|---|
| anchor (`anchor.py`) | 23921 | Stand-in for a TPM NV counter or transparency-log head. State `(version, digest)` is fsynced on every change and every increment is appended to its own `anchor.log`. Socket ops are `read` and `increment(to)`; only `to = version + 1` from the gate UID is accepted. There is no reset or decrement. |
| gate (`gate.py`) | 23922 | Budget (cap) + one-use-nonce ledger in SQLite (`journal_mode=DELETE`, `synchronous=FULL`). Each record extends a SHA-256 digest chain `d_v = sha256(d_{v-1} ‖ op_v)`. |
| client | 23923 | Forked by the harness, setuid; the gate authenticates it with SO_PEERCRED. |

**A spend runs in this order:**
1. Check store `(version, digest)` == anchor.
2. Refuse a used nonce, or an amount over the cap.
3. Commit `v+1` to the store.
4. `increment(v+1, d_{v+1})` on the anchor.
5. Perform the effect: an fsynced line in `effects.log`, outside the snapshotted store.

**The same check runs on every operation and at startup:**

| store vs anchor | action |
|---|---|
| equal | OK; a missing effect for that version is re-performed, deduplicated by `(version, digest)` |
| store = anchor + 1, chain valid, and the store's digest at the anchor's version equals the anchor's digest | RECOVER: increment, then perform the effect (the crash window) |
| anything else | FAIL CLOSED: every later operation is refused |

**The harness is the untrusted operator.** It:
- copies the database file (snapshots);
- restores an older copy, either cold (gate stopped, then restarted) or hot (copied in place under the running
  gate);
- deletes the store;
- crashes the gate (`os._exit`) at three points: `after_commit` (store committed, anchor not incremented),
  `after_anchor` (anchor incremented, effect not performed) and `after_effect` (effect performed, client not
  answered).

**Independent reconciliation.** It reads only the anchor's own `anchor.log` (written by the anchor UID) and
`effects.log`, never the gate database. It flags:
- `anchor_log_not_contiguous` (versions not exactly 1..n);
- `effect_not_anchored` (an effect `(version, digest)` absent from the anchor log);
- `anchored_version_without_exactly_one_effect`;
- `effect_versions_not_increasing`;
- `duplicate_nonce`;
- `over_cap`.

**Out of scope:**
- Forged records. An operator who writes a new, validly chained record, rather than restoring an old one, is outside
  this operator model. Record integrity (for example a MAC with a key the operator lacks) is a separate premise, as
  in the Lean model. The predecessor-digest and chain checks guard against forgery and tampering. They are exercised
  only by unit tests (`test_ar.py`: `test_crash_window_recovery_needs_matching_predecessor`,
  `test_tampered_chain_refused`, `test_fork_detected_by_digest`). §7 shows that the runtime hypotheses cannot
  distinguish a gate without them.
- Rolling back the anchor itself. Its monotonicity is the premise; a real TPM or transparency log is not tested.
- Multiple gates sharing one anchor.
- Availability under anchor outage.

## 2. Environment and host safety

**Host and command:** this OCI ARM64 host, `sudo -n /bin/python3 -B experiments/anti-rollback/harness/run_ar.py`
(Python 3.9, SQLite 3.34.1). Root is needed only to run three separate numeric UIDs.

**UIDs:** bare numbers 23921–23923. No accounts are created. Preflight refuses to start if any process already runs
under them.

**Workloads are benign:**
- a few dozen small SQLite transactions and file appends per case;
- file copies inside the run directory;
- no network, no cgroups, no host cron, at or systemd timers.

**Files:** only under a fresh `/var/tmp/ar-run-*`, which is removed at the end, and the `--out` receipt directory.

**Cleanup:**
- after each case, the gate and anchor are stopped;
- after every case, `/proc` is scanned for the reserved UIDs, and any residue aborts the run;
- at the end, kill-by-UID runs, verified by `/proc`.

**Wall limit:** 120 s.

## 3. Constants (fixed; calibrated in §7)

| constant | value | | constant | value |
|---|---|---|---|---|
| CAP (H1, H2, H4) | 100 | | AMOUNT (each spend) | 20 (5 spends fill the cap) |
| H3_CAP | 300 | | H3 ops | 21: 18 fresh, 1 replay, 1 over the cap, 1 that fits |
| H3_RESTART_EVERY / H3_BACKUP_EVERY | 5 / 4 ops | | CRASH_RC | 17 |
| RECOVERY_BOUND (restart → READY, H2) | 1.0 s | | READY_TIMEOUT / STOP_TIMEOUT / CALL_TIMEOUT | 10 / 5 / 10 s |
| WALL_LIMIT | 120 s | | repetitions | 5 |

**Cases per repetition:** H1 7 variants, H2 5 variants, H3 1, H4 1. That makes 70 cases per evidence run. Every case
runs on a fresh deployment.

## 4. Hypotheses (every case must pass in all 5 repetitions)

**H1. Rollback is refused (fail closed).** Setup: spends n1..n5 (cap reached; anchor at 5), with snapshots S0
(genesis), S3 and S4.

Variants:
- `cold-genesis`, `cold-mid` (S3), `cold-prev` (S4) and `cold-delete` (store deleted): gate stopped, store restored,
  gate restarted;
- `hot-mid` and `hot-prev`: restored in place under the running gate.

Pass:
- **cold variants:** startup reports `rollback`;
- the replays n4, n5 and n1, and a fresh nonce f1 within the restored budget, are all refused with `fail closed`;
- status reports `rollback`;
- anchor state, anchor log and effect log are unchanged (identical records);
- reconciliation is clean, with 5 effects and the anchor at 5.

Variant `anchor-api` passes if all of the following are refused:
- root and client increments;
- gate-UID increments to `v`, `v−1` and `v+2`;
- a gate-UID `set` op;
- a client `read`.

In addition, the gate still serves, and the anchor and effects are unchanged.

**H2. Crash recovery admits no rollback.** Setup: n1..n3 with snapshots S2 and S3. Then a crash is set at a point and
n4 is sent.

Pass for every variant: n4 gets no reply, the gate exits with code 17, and restart → READY ≤ RECOVERY_BOUND.

- **`after_commit`:** startup reports ok with recovery `anchor_incremented` v4.
- **`after_anchor`:** startup reports ok with recovery `effect_reperformed` v4.
- **`after_effect`:** startup reports ok with no recovery.

  For all three of these:
  - anchor `(version, digest)` == store;
  - a retry of n4 is refused (`nonce already used`);
  - n5 lands at v5;
  - effects are exactly n1..n5 at versions 1..5;
  - reconciliation is clean.
- **`after_commit+restore-pre`:** the operator restores S3 (the crash window, anchor still 3). Startup reports ok with
  no recovery. The retry of n4 lands once at v4; n5 lands at v5; effects are exactly n1..n5; reconciliation is clean.
- **`after_commit+restore-older`:** the operator restores S2 (older than the anchor). Startup reports `rollback`;
  n4, n3 and f1 are refused; effects are n1..n3; reconciliation is clean at anchor 3.

**H3. Usefulness (no spurious refusals).**
- **Setup:**
  - 21 ops, checked against a reference ledger;
  - a gate restart (stop, start) every 5 ops;
  - a backup copy every 4 ops (never restored).
- **Pass:**
  - zero spurious refusals (the reference accepts, the gate refuses);
  - zero wrong acceptances;
  - exactly 2 refusals (the replay and the over-cap op);
  - every restart reports ok with nothing recovered;
  - final status ok, with spent equal to the reference;
  - reconciliation is clean, with effects = anchor version = 19 accepted ops and total = reference.

**H4. Negative control (anchor disabled).** The same gate runs with `--anchor-off` (`AR_NEGATIVE_CONTROL=1`; no
anchor process). Setup: n1..n5, snapshot S3, cold restore of S3, restart.

Pass (all four):
- startup reports ok;
- the replay of consumed nonce n4 lands;
- fresh f1 lands past the cap;
- reconciliation (effect-only checks, no anchor log) flags BOTH `duplicate_nonce` AND `over_cap`.

A FAIL of H4 means the test cannot detect the failure it is meant to rule out. In that case the run is reported FAIL.

## 5. Runs, re-runs and stopping

- **One evidence run:** `--kind evidence --reps 5 --out experiments/anti-rollback/evidence/run-1`.
- **INFRA-ERROR:** an INFRA-ERROR at preflight (not root, or reserved-UID processes present) allows one further run,
  to `run-2`. Both are kept.
- **Failures:** any hypothesis failure is final for this ID and is reported as is.
- **Stop** on residue, on the wall limit, or on any effect outside the run directory, the receipt directory or the
  reserved UIDs.

## 6. What a result licenses

**Pass:** on this host, a SQLite ledger bound to an external monotonic `(version, digest)` anchor, under a
restore/delete/crash operator:
- refuses every operation after any restore of an older snapshot (cold or hot) or deletion of the store, so no nonce
  replay or budget re-spend lands, as confirmed by independent reconciliation against the anchor's own log and the
  effect log;
- recovers each of the three crash points to exactly one effect per anchored version;
- refuses nothing that a correct ledger accepts when nothing is rolled back.

The same restore against the same gate without the anchor demonstrably replays and re-spends.

**Limits:**
- This is CONDITIONAL on the anchor's own monotonicity and integrity: a separate-UID process stands in for a TPM NV
  counter or transparency log.
- It does not cover record forgery (unit tests only) or anchor rollback.
- It is not deployment assurance, and it makes no claim about real HSM, TPM or transparency-log products.

**Ledger:** if PASS, the ledger row for `anti_rollback` may record runtime evidence for the restore/crash operator
model only.

## 7. Dry-run calibration (before freezing)

All dry runs went to the session scratchpad, not to the repo. Code was identical except the two constants noted
below. Every run had cleanup ok: no reserved-UID process left, and the work directory removed.

| run | reps | wall | H1 | H2 | H3 | H4 (control) | H2 restart → READY |
|---|---|---|---|---|---|---|---|
| dry1 | 1 | 4.0 s | 7/7 | 5/5 | 1/1 | 1/1 detected | max 0.048 s |
| dry2 | 5 | 20.1 s | 35/35 | 25/25 | 5/5 | 5/5 detected | max 0.058 s, median 0.046 s |
| dry3 | 5 | 20.6 s | 35/35 | 25/25 | 5/5 | 5/5 detected | max 0.052 s, median 0.045 s |
| dry4 | 5 | 20.7 s | 35/35 | 25/25 | 5/5 | 5/5 detected | max 0.058 s, median 0.044 s |
| dry5, under CPU load (one busy loop per core, both cores) | 5 | 38.9 s | 35/35 | 25/25 | 5/5 | 5/5 detected | max 0.168 s, median 0.100 s |
| dry6, final constants and files | 5 | 21.4 s | 35/35 | 25/25 | 5/5 | 5/5 detected | max 0.060 s, median 0.045 s |

dry1–dry5 ran with RECOVERY_BOUND = 2.0 s and WALL_LIMIT = 300 s; these were then fixed at 1.0 s and 120 s.

**Other observations:**
- Per-spend latency in H3 includes the client fork and five fsyncs. Unloaded, the per-case median is 16.6–19.4 ms
  and the max is 28.8 ms; under load, the median is 21.7–29.0 ms and the max is 47.9 ms.
- The longest single case took 0.74 s unloaded and 1.39 s under load.
- In H4, reconciliation also flagged `effect_versions_not_increasing`; this is not required.

**Bounds:**
- RECOVERY_BOUND 1.0 s is 6× the loaded maximum (0.168 s) and 17× the unloaded one (0.060 s).
- WALL_LIMIT 120 s is 3× the loaded wall time and about 6× the unloaded one (20–21 s).

**Sensitivity (mutation dry runs, H1 + H2, 1 rep, scratch copies of the harness):**
- **Gate that never consults the anchor (`check()` returns at once, anchor still incremented):** fails 6/7 H1
  variants (all but `anchor-api`) and 3/5 H2 variants (`after_commit`, `after_anchor`, `after_commit+restore-older`).
  Detected.
- **Recovery that accepts any store ahead of the anchor (no chain or predecessor check):** passes everything. This
  is expected and is why §1 lists forgery as out of scope. Without forged records, a store at anchor + 1 always
  extends the anchored record, because the gate commits only from store == anchor and the anchor's digest at each
  version never changes. Those checks matter only against forgery and are covered by unit tests.

**Unit tests:** `test_ar.py`, 12 tests, pass under Python 3.9 and 3.14.

## 8. Pinned artifacts (SHA-256 at freeze)

Commit: `fb0d9fc52799827e4d0777ceee7f3d48614a9cfd`.

| Path | SHA-256 |
|---|---|
| `experiments/anti-rollback/harness/anchor.py` | `e8e65292ac64a2481d06a05a853345bece475e6cc07381e89eecef19b2a46a6e` |
| `experiments/anti-rollback/harness/gate.py` | `5249c0da7ef381f71adc2f86904215fd6aa134ccd1778a03a159529e227791d8` |
| `experiments/anti-rollback/harness/run_ar.py` | `9940c78c6af05d57aee3efd32e71023763f2fec29324fd51121b85b63fda14d9` |
| `experiments/anti-rollback/harness/test_ar.py` | `706176644c7835eaf3a9b590456ec13a2b86c1daed28fbbb59e044d05d549b2d` |
| `experiments/anti-rollback/harness/README.md` | `ded49c4c70c515a5aba4e621ce48dfb35644506196ede280f9aff8f520557491` |
| `ControlStack/Core/AntiRollback.lean` | `3efc33a69338d07b822a9a943c6becb15b3f9f2190e6b755091a10121dc51c8d` |
