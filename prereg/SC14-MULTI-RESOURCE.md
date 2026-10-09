# Preregistration: SC-14 per-job multi-resource budgets (CPU time, memory, pids, rate, expiry)

**ID:** `PREREG-SC14-MULTIRES-v1`. **Written:** 2026-10-09, before any evidence run (after the dry runs in §7).
**Status: FROZEN 2026-10-09** (frozen by the orchestrator before any evidence run; pins filled; committed with its harness).

**Freeze:**
1. Delete this line and fill §8.
2. Commit this file together with `scenarios/SC-14/harness/`.

## 1. Claim under test and scope

**Model:** `ControlStack/Scenarios/SC14Runaway.lean`.
- `sc14_safe`: cumulative actual usage of every resource stays within its cap, every window stays within its rate
  limit, and no step runs after the expiry.
- Necessity witnesses used here: `aggregate_cap_breaks` (control H2), and the shapes of `rate_burst_breaks` and
  `no_expiry_breaks` (H3 and H4 test the deployed side).

**What the harness implements (`jobs.py`).** A job is a cgroup v2 `sc14-test/job-<name>` with a budget vector. It is
metered by the kernel or by the trusted controller, never by the job's report:

| component | enforcement | metered by |
|---|---|---|
| memory | `memory.max`, with `memory.swap.max = 0` so swapping cannot sidestep the cap | `memory.peak` |
| pids | `pids.max` | `pids.peak` |
| rate | `cpu.max` quota per 100 ms period | `cpu.stat` |
| cumulative CPU time | the controller polls `cpu.stat` every 10 ms and writes `cgroup.kill` at the budget | `cpu.stat` |
| lease expiry | the controller writes `cgroup.kill` at the deadline and refuses later launches | timestamps |

**Network egress is NOT in this harness.** The SC-07 namespace and nftables quota covers bytes on its own; combining
the two is not attempted. This test therefore covers three kernel resources plus CPU time and expiry, not the
model's network dimension.

**Not tested and not claimed:**
- tokens or API spend;
- descendants that escape the cgroup (that is SC-12 and SC-28);
- adversarial workloads;
- multi-job global caps (that is SC-28);
- other hosts.

## 2. Environment and host safety

- **Host:** this OCI ARM64 host, cgroup v2, swap present (hence `memory.swap.max = 0`). Run as
  `sudo -n /bin/python3 -B scenarios/SC-14/harness/run_sc14.py`.
- **Cgroups:** only under `/sys/fs/cgroup/sc14-test`. Limits are written and read back before any process enters:
  pids.max ≤ 64, memory.max ≤ 128 MiB, cpu.max ≤ 0.5 CPU.
- **UIDs:** bare numbers 23905–23909; jobs run as 23905. No accounts are created.
- **Workloads are benign and bounded:**
  - CPU loops ≤ 5 s;
  - allocations ≤ 96 MiB (64 MiB is used, against a 32 MiB cap);
  - ≤ 24 fork attempts, with no retry;
  - sleeps ≤ 20 s.
- **Cleanup:** after every hypothesis, `cgroup.kill`, then rmdir, then kill-by-UID, verified by `/proc`. Any residue
  aborts the run.

## 3. Constants (fixed; calibrated in §7)

**Budget:** CPU 0.5 s, memory 32 MiB, pids 8, rate 0.5 CPU, expiry 10 s.

| constant | value | | constant | value |
|---|---|---|---|---|
| CPU_TOL | 50 ms of CPU | | RATE_QUOTA (H3) | 20000/100000 (0.2 CPU) |
| GREEDY_CPU_S | 3.0 s | | RATE_TOL | 0.03 CPU |
| GREEDY_MIB | 64 | | RATE_WARMUP, RATE_WINDOW | 0.3 s, 2.0 s |
| GREEDY_FORKS | 20 (hold 1.0 s) | | EXPIRY_S (H4) | 1.0 s |
| AGG_CAP (H2) | 3.0, the sum of the three fractions | | EXP_TOL | 0.05 s |
| KILL_BOUND / REAP_BOUND | 1.0 s / 5.0 s | | OK_EXPIRY_S (H5) | 5 s |

**Repetitions:** 5 per hypothesis.

## 4. Hypotheses (each must pass in all 5 repetitions)

- **H1 Per-resource caps hold.** Three greedy jobs, each shown to have TRIED to exceed:
  - **CPU:** killed for its CPU budget (it did not finish), and `usage_usec` ≤ 0.5 s + CPU_TOL.
  - **Memory:** an OOM kill is recorded and the job did not finish, and `memory.peak` ≤ `memory.max`.
  - **Pids:** at least one fork got EAGAIN, and `pids.peak` ≤ `pids.max`.
- **H2 Control (`aggregate_cap_breaks`).** Only the aggregate is enforced. A CPU-heavy job's usage EXCEEDS the
  intended per-resource CPU cap + CPU_TOL, i.e. it is detected.
- **H3 Rate.** The CPU rate over RATE_WINDOW is ≤ 0.2 + RATE_TOL, and `nr_throttled` rose (the cap was binding).
- **H4 Expiry.** A job still running at its deadline:
  - is killed for expiry;
  - the kill is written ≤ EXP_TOL after the deadline;
  - zero live job processes within KILL_BOUND of the deadline (independent `/proc`);
  - a later launch into it is refused.
- **H5 Usefulness.** A within-budget job (0.2 s CPU, 8 MiB, 3 children):
  - exits 0 and reports DONE;
  - is not killed and finishes before its expiry;
  - its metered usage is within every cap.

## 5. Runs, re-runs and stopping

- **One evidence run:** `--kind evidence --reps 5 --out scenarios/SC-14/evidence/run-1`.
- **Infrastructure errors:** an INFRA-ERROR at preflight allows one further run, to `run-2`. Both are kept.
- **Failures:** a hypothesis failure is final for this ID.
- **Stop** on residue, on the wall limit, or on any effect outside `sc14-test`, the run directory or the reserved
  UIDs.

## 6. What a result licenses

**Pass:** on this host, a per-job budget vector over CPU time, memory, pids, CPU rate and lease expiry is enforced by
the kernel and a trusted meter within the stated tolerances. An aggregate-only cap demonstrably does not bound an
individual resource. This is CONDITIONAL. It covers no network dimension, no token spend and no global multi-job
cap, and it is not deployment assurance.

## 7. Dry-run calibration (before freezing)

**Dry runs:** `sc14-dry1` (1 rep) and `sc14-dry2` (5 reps, 50 s wall) both passed every hypothesis, and the H2
control was detected every time.

| quantity | observed (5 reps) | bound |
|---|---|---|
| CPU usage at the budget kill | 501 254–504 127 µs | 550 000 µs (overshoot ≤ 4.1 ms against 50 ms) |
| `memory.peak` | 33 554 432 = `memory.max` every time | ≤ cap (an OOM kill each time) |
| `pids.peak` | 8 every time (13 refused forks each time) | ≤ 8 |
| aggregate control CPU | 1.36–1.37 s | detected, > 0.55 s |
| rate | 0.198–0.204 CPU | 0.23 |
| expiry kill lag | 0.5–8.4 ms | 50 ms |
| job processes gone after the deadline | 17–32 ms | 1.0 s |
| H5 job | 0.44–0.53 s, 0.15–0.17 s of CPU | within caps and expiry |

Every bound has at least a 6× margin over the observed maximum.

## 8. Pinned artifacts (SHA-256 at freeze)

Commit: `065b57e47d47dcb548d686150cea11386ba3fc67`.

| Path | SHA-256 |
|---|---|
| `scenarios/SC-14/harness/cgctl.py` | `ba553bcd6f27b6cba84a6d7c7217f923073689ce2b9d960185810b91ec9ce1c2` |
| `scenarios/SC-14/harness/jobs.py` | `77084bc6a181fcbb7da20f397fe74312e4cc1533bfdeed01dc69216c66f224e5` |
| `scenarios/SC-14/harness/workloads.py` | `2ae6e888022b470b77784ddcd957c11567ba7ed7012fee481e155122cabda9f8` |
| `scenarios/SC-14/harness/run_sc14.py` | `fcf5b167eb3b83c49b4e8d57898448e8c09eb838ca69e6af66a3d9c84e0f21b2` |
| `ControlStack/Scenarios/SC14Runaway.lean` | `5b3828bb3dca7035a2c0d19276b80fc53b4c551d4318f57c20dbd1d1a6609d50` |
