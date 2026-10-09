# Preregistration: DC-1 fencing sink, single-host rehearsal (v1)

**ID:** `PREREG-DC1R-SINGLEHOST-v1`. **Written:** 2026-10-09, before any dry run or evidence run.
**Freeze:** this file's Git commit and SHA-256 are recorded in every receipt. After the evidence run starts, this file
is not edited. A change needs a new ID (`-v2`), a new file and a new run. The earlier run is kept.

**Relation to DC-1:** this is a one-host rehearsal of `prereg/DC1-DISTRIBUTED-HALT-DRAFT.md` (STACK-MAP §4 item 4).
It does **not** satisfy DC-1, which needs ≥ 3 hosts, a real network and a firewall-enforced partition. Here
"delivery delay" is a sleep in the controller and "partition" means the controller never writes HALT to one worker.

## 1. Claim under test and its scope

**Model:** `ControlStack/Families/F3/DistributedHalt.lean` (SHA-256 recorded in every receipt). The run checks that a
small, real effect sink and worker pool on one host behave as the model's premises and conclusions say, for benign
workers:

- **Unfenced:** after HALT at t0, the number of effects accepted at the sink is bounded by the delivery delays and
  in-flight latency, n·ρ·(L + Δ).
- **Fenced:** once the sink's epoch is bumped (t0 + ε), it accepts **no** effect from a holder of the old epoch,
  whether or not that worker ever received HALT.
- **Controls:** without fencing, a worker that never receives HALT lands effects without bound; with fencing, a worker
  that holds the new epoch still lands effects. These are the model's two necessity witnesses.

**Implementation:** `experiments/DC-1-rehearsal/harness/`:
- `sink.py`: single-threaded, append-only effect sink; stamps every landing with its own CLOCK_MONOTONIC and applies
  the acceptance rule below;
- `worker.py`: benign worker that emits small JSON effects at rate ≤ ρ and obeys HALT on stdin;
- `analyse.py`: the measurements and decision rules over the stored sink log, plus mutation self-tests;
- `run_dc1r.py`: the controller, the repetitions, the checks and the receipt.

**Correspondence with the model.**

| model (`DistributedHalt.lean`) | this run |
|---|---|
| node i < n | worker process i < N = 8 |
| `Rate ρ e`: ≤ ρ effects per tick | a worker schedules its next effect 1/ρ after the previous one's initiation stamp, so any window of length w holds ≤ ρ·w + 1 of its effects; ρ = 50 /s. Checked from the stamps. |
| `HaltAbsorbs`: nothing initiated after t0 + δ_i | after reading HALT the worker never emits again. Checked: no effect has an initiation stamp after the worker's HALT receipt stamp. |
| `Delivered n Δ δ` | the controller writes HALT to worker i at t0 + δ_i, δ_i = Δ·i/(N − 1), Δ = 0.20 s; realised delays δ̂_i are the workers' receipt stamps minus t0. |
| `Latency L lat` | landing stamp (sink) minus initiation stamp (worker), one host, one CLOCK_MONOTONIC; L̂ = the maximum. |
| `HoldsOld e0 ep` | every worker starts with e0 = 1; only the controller sends the new epoch (only in H4). |
| `accepts fence t0 ε e0 (t, ep)` = ¬fence ∨ t < t0 + ε ∨ ep ≥ e0 + 1 | the sink accepts iff fencing is off or ep ≥ its current epoch; the current epoch is e0 until the BUMP takes effect at tF and e0 + 1 afterwards. Since every worker holds ≥ e0, this equals the model's rule with t0 + ε := tF. |
| ε (sink learns of the halt) | ε̂ = tF − t0, both sink stamps (MARK and BUMP records); the controller sends BUMP at t0 + 0.05 s. |
| `sinkRun` processes events in any order | the sink processes effects and control commands one at a time in one loop; landing time = processing time. |
| `countP (t0 ≤ ev.1)` of accepted | A_t0 = accepted effects with sink stamp ≥ t0; A_tF = accepted with sink stamp ≥ tF. |
| discrete ticks | continuous ns. With real time, each node contributes ≤ ρ·w + 1 in a window of length w, so the bound gains up to +1 per node (+N in total); this is the floor of the tolerance TAU_A (§3.0). |
| global budget G | not exercised (no budget at the sink). |

**Not tested here, and not claimed:**
- **More than one host, a real network, clock skew.** All stamps are on one host; there is no cross-host clock.
- **A real partition.** The "partitioned" worker is one the controller never writes HALT to.
- **Adversarial workers.** No worker forges epochs, bypasses the sink, floods, or attacks the sink or controller.
  The H4 leak is done by the controller on purpose, to show the premise is needed.
- **Effects that bypass the sink**, a consensus-backed epoch store, the global budget G, and durability of the sink
  log (it is fsync'd once, at STOP, and only used for analysis).
- **Production schedulers or networks.**

## 2. Environment and trust

- **Host:** the OCI ARM64 Linux box running this repository (single host, shared with other work). No root: the runner
  refuses to run as root.
- **Interpreter:** the system Python (`/bin/python3`, 3.9); every child runs with `-I -S -B`.
- **Processes:** per repetition one sink and 8 workers, all children of the runner, all as the invoking user.
- **Sockets:** Unix stream sockets only (effects, control), mode 0600, in a fresh `/var/tmp/dc1r-run-*` directory
  (mode 0700). No TCP, no network.
- **Trusted:** the kernel, CPython, the sink and the runner at the recorded hashes.
- **Untrusted:** nothing in the adversarial sense; workers are benign by construction.
- **Receipt contents:**
  - the Git commit and dirty status, the SHA-256 of every harness file, of this file and of `DistributedHalt.lean`;
  - the calibration status and tolerance read from this file;
  - `uname`, the Python version, load average at start and end;
  - per repetition: the full sink log (gzip), every worker's READY/HALTED/EPOCHSET reports, the controller timeline
    (mark, each HALT write, bump, kill), all measurements and every check as expected / observed / pass.

**Host-safety bounds** (part of this registration):
- every child process exits by itself after 30 s;
- the whole run has a 115 s wall limit (SIGALRM);
- every repetition kills its children in a `finally` block; after each repetition an independent `/proc` scan for
  the run's work directory in a command line must be empty, or the run aborts;
- the work directory is removed at the end; total load is 8 × 50 small messages per second.

## 3. Hypotheses and decision rules

**Fixed parameters:** N = 8, ρ = 50 /s, e0 = 1, Δ = 0.20 s with δ_i = Δ·i/7, ε (controller) = 0.05 s, warm-up 0.5 s
of emission before t0. The designated partitioned worker is worker 7 (H2–H4). Observation after t0: H1 1.0 s,
H2 2.0 s, H3 3.0 s, H4 1.5 s; then the workers are killed and the sink is stopped (it first drains its sockets).

**Measured, per repetition, from the stored sink log:** t0, tF, ε̂ = tF − t0, L̂, δ̂_i and Δ̂ = max δ̂_i over the
workers that received HALT, A_t0, A_tF, per-worker counts, and time to quiescence (last accepted landing − t0).
The bounds use the measured values: B_unf = N·ρ·(L̂ + Δ̂) (`landed_after_le` with Δ := Δ̂, L := L̂, so the
premises hold by definition) and B_fen = N·ρ·(L̂ + ε̂) (`fenced_window`).

**Checks common to every repetition (premise and integrity checks):**
- **Rate:** every worker's initiation spacing ≥ 1/ρ − 10 µs;
- **Latency sanity:** L̂ ≤ 0.05 s;
- **Integrity:** per worker, sink sequence numbers are 0, 1, 2, … with no gap, and no malformed line;
- **Rule:** every sink decision equals the acceptance rule recomputed from the logged epoch and the BUMP record;
- **Delivery:** exactly the intended workers report HALT receipt (all 8 in H1; workers 0–6 in H2–H4);
- **HaltAbsorbs:** no effect has an initiation stamp after its worker's HALT receipt.

**Pass rule:** each hypothesis runs **5 repetitions**, each on fresh processes. A hypothesis passes only if every
check passes in all 5. An exception inside a repetition fails it. For the controls (H3, H4, flagged
`NEGATIVE_CONTROL` in the receipt) "pass" means the control **fired**: the bad event the model predicts was observed.

### 3.0 Tolerance calibration (fixed before any evidence run)

There is one tolerance, TAU_A (effects), used by H1, H2-window and H3. Its floor is N = 8, the real-time
discretisation term (§1 table). Rule: after at least two complete dry runs (5 repetitions each, all hypotheses) with
the harness at its final state, TAU_A = max(8, ⌈1.5 × E⌉), where E is the largest excess A_t0 − B over all H1
repetitions (B = B_unf) and all H2 repetitions (B = B_fen) of those dry runs, or 0 if no repetition exceeded its B.
The value and the dry-run receipts it came from are written below, the status line is set to FIXED, and the harness
constant is set to the same value **before** the commit that freezes this file. The runner refuses an evidence run
unless the status is FIXED and the harness value equals the value here.

```
CALIBRATION-STATUS: FIXED
TAU_A = 8
```

Calibration record (2026-10-09). Two complete dry runs, 5 repetitions × H1–H4 each, harness at its final state,
receipts `dc1-dry-cal1` and `dc1-dry-cal2` (session scratch directory; dry, not evidence). Both overall PASS.
- H1 (10 reps): A_t0 38–41, B_unf 80.3–83.0; excess A_t0 − B_unf from −43.6 to −40.3.
- H2 (10 reps): A_t0 16–18, B_fen 20.3–22.2; excess from −6.2 to −2.9; A_tF = 0 in all.
- No repetition exceeded its bound, so E = 0 and TAU_A = max(8, ⌈1.5 × 0⌉) = **8** (the discretisation floor).
- Context: L̂ 0.4–18.4 ms, Δ̂ 200.1–200.2 ms (H1) and 171.6–173.8 ms (H2–H4), ε̂ 50.1–52.0 ms. H3 A_t0 175–180
  against B_unf + 8 ≈ 77–80. H4: 70–72 accepted after tF from worker 7, none from others.
- An earlier one-repetition debugging dry run (`dc1-dry0`) also passed. It is not used for calibration.

### H1 Unfenced HALT window (`landed_after_le`; also `initiated_after_le`, `unfenced_composed` without budget)

Fencing off. All 8 workers receive HALT at t0 + δ_i.
- **Pass:** A_t0 ≤ B_unf + TAU_A.
- **Sanity:** Δ̂ ≤ 0.25 s; A_t0 ≥ 1 (effects really do land after t0, so the bound is not met vacuously).
- **Sensitivity:** the H1 rule fails on a copy of the stored log with enough accepted landings injected after t0 to
  exceed B_unf + TAU_A.
- Reported, not decided: the per-node form Σ_i ρ·(L̂ + δ̂_i), and time to quiescence.

### H2 Fenced sink with a partitioned worker (`fenced_after_eps`, `partition_fenced`, `fenced_window`)

Fencing on. Workers 0–6 receive HALT at t0 + δ_i; worker 7 never does and keeps emitting with epoch e0.
- **Pass (main):** A_tF = 0: zero accepted landings with sink stamp ≥ tF = t0 + ε̂.
- **Pass (window):** A_t0 ≤ B_fen + TAU_A.
- **Sanity:** ε̂ ≤ 0.10 s.
- **Non-vacuity:** worker 7 has ≥ 0.8·ρ·(2.0 − ε̂) rejected landings after tF (it kept trying).
- **Sensitivity:** the H2 rule fails on a copy of the stored log with one accepted old-epoch landing injected after
  tF, and the rule-consistency check flags that record.

### H3 Control: unfenced sink, partitioned worker (`partition_unbounded`)

Fencing off. Workers 0–6 receive HALT; worker 7 never does.
- **Fires (pass) iff all hold:** worker 7's accepted landings in [t0, t0 + c) for c = 0.75, 1.5, 2.25, 3.0 s are
  strictly increasing; their slope between the first and last checkpoint is ≥ 0.8·ρ = 40 /s; and A_t0 exceeds the
  bounded-delivery bound B_unf + TAU_A (B_unf computed from the 7 workers that did receive HALT). Linear growth over
  the observation window is the run's finite stand-in for "unbounded": the count grows with run length at the
  worker's rate, so any fixed bound is exceeded by a long enough run.
- **Sensitivity:** the detector does not fire on a copy of the log with worker 7's after-t0 landings removed.

### H4 Control: token leak (`token_leak`)

Fencing on. Worker 7 is partitioned and, 0.2 s before t0, the controller hands it the new epoch e0 + 1 (a deliberate
violation of `HoldsOld`).
- **Precondition:** worker 7 reports holding epoch e0 + 1 before t0.
- **Fires (pass) iff:** ≥ 1 of worker 7's landings is accepted at or after tF, no other worker has an accepted
  landing at or after tF, and every accepted landing after tF carries epoch e0 + 1.
- **Sensitivity:** the detector does not fire on a copy of the log with worker 7's after-tF landings marked rejected.

**Overall pass:** H1–H4 all pass (both controls fire), the run is not aborted, and no process of the run survives.

## 4. Runs, re-runs and stopping

- **Dry runs** use `--kind dry`, write to scratch directories, and are not evidence. They are used for debugging and
  for the calibration in §3.0.
- **The evidence run** is exactly one invocation of:
  ```
  /bin/python3 -B experiments/DC-1-rehearsal/harness/run_dc1r.py --kind evidence --reps 5 --out <new dir>
  ```
  - It runs from a commit in which this file and every harness file are committed and unmodified, and this file says
    `CALIBRATION-STATUS: FIXED` with the harness's TAU_A. The runner refuses otherwise.
  - It runs all four hypotheses. The receipt directory is kept, whatever the outcome.
- **Infrastructure errors:** a re-run is allowed only for a preflight failure before any hypothesis starts (wrong
  interpreter, a stale process of an earlier run, a dirty tree, calibration not FIXED). At most one re-run; both
  receipts are kept.
- **Failures are final:** a hypothesis failure, including one caused by load on the shared host, is recorded as
  FAILED. It is never re-run under this ID. A re-run with changed bounds needs `-v2`.
- **Stop:** the runner aborts the whole run, with cleanup, if a process of the run survives a repetition or the
  115 s wall limit is reached.

## 5. What a pass licenses

On this host, for benign workers, with HALT delivery simulated by controller-side delays:
- an unfenced sink accepts at most N·ρ·(L̂ + Δ̂) + TAU_A effects after HALT, with the measured L̂ and Δ̂;
- an epoch-checking sink accepts **zero** old-epoch effects once its epoch is bumped, including from a worker that
  never received HALT, and at most N·ρ·(L̂ + ε̂) + TAU_A after t0;
- the experiment can see both failure modes the model predicts (partition without fencing; a leaked epoch with
  fencing).

A pass is a rehearsal of the DC-1 measurement and analysis pipeline and an operational check of the `sink_fencing`
premise for this sink implementation. It is not evidence about real networks, partitions, clock skew, other sinks or
adversarial workers, and it does not discharge DC-1.

## 6. Mapping to the Lean model

| hypothesis | theorem(s) in `ControlStack.DistributedHalt` | role |
|---|---|---|
| H1 | `landed_after_le` (and `initiated_after_le`, `unfenced_composed`) | conclusion checked under realised premises |
| H2 | `fenced_after_eps`; `partition_fenced`; `fenced_window` | conclusion checked, including with a partitioned worker |
| H3 | `partition_unbounded` | necessity witness reproduced (negative control) |
| H4 | `token_leak` | necessity witness reproduced (negative control) |
