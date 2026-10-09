# Preregistration: SC-12 session lineage — nothing a session started survives its end

**ID:** `PREREG-SC12-LINEAGE-v1`. **Written:** 2026-10-09, before any evidence run (after the dry runs in §7).
**Status: FROZEN 2026-10-09** (frozen by the orchestrator before any evidence run; pins filled; committed with its harness).

**Freeze:**
1. Delete this line and fill §8.
2. Commit this file together with `scenarios/SC-12/harness/`.

The runner also refuses an evidence run if git reports the harness or this file modified.

## 1. Claim under test and scope

**Model:** `ControlStack/Scenarios/SC12Persistence.lean`. The theorems: `sc12_safe` (every live entity is registered,
and its lineage's session is active, not ended) and `no_fire_after_end`. Also `AuthInstancesB.sc12_safe_authenticated`,
where the issuer is the platform identity, here the caller's UID via SO_PEERCRED.

**Necessity witnesses exercised as controls (H4):**
- `foreign_registration_survives`;
- `registry_bypass_survives`;
- `parent_only_revocation_survives`.

**What the harness implements:**
- A session is a cgroup v2 `sc12-test/sess-<name>` owned by one reserved UID. Everything the session's workload
  starts is in it by inheritance: children, grandchildren, and a session-detached (`setsid`) daemon.
- Scheduled jobs exist only in the controller's own trusted scheduler. The host's cron, at and systemd timers are
  never used.
  - A job is registered over a Unix socket. The caller's UID is read from SO_PEERCRED and selects the session.
  - At its due time the scheduler launches the job as the session UID, inside the session cgroup.
  - A launch and end-session take the same lock, so no job can be placed into a session after its `cgroup.kill`.
    This design point was found and fixed before any dry run, and is unit-tested.
- **End-session:** refuse new registrations, cancel every pending job of the session, then write `cgroup.kill`.

**Not tested and not claimed:**
- creation paths other than processes and this scheduler: accounts, host cron/systemd, cloud resources,
  credentials;
- adversarial (evasive) workloads;
- effects caused while the session was live;
- other hosts.

## 2. Environment and host safety

- **Host:** this OCI ARM64 host, cgroup v2, run as `sudo -n /bin/python3 -B scenarios/SC-12/harness/run_sc12.py`.
- **Cgroups:** only under `/sys/fs/cgroup/sc12-test`. Limits are written and read back before any process enters:
  pids.max ≤ 64 (32 per session), memory.max ≤ 128 MiB (64 MiB per session), cpu.max ≤ 0.5 CPU.
- **UIDs:** bare numbers 23901–23904; no accounts are created. Session A is 23901, session B is 23902.
- **Workloads (`workloads.py`) are benign and bounded.** Lifetime ≤ 20 s, ≤ 3 children with 1 grandchild each, one
  daemon, no signal handling, no evasive behaviour.
- **Cleanup:** after every hypothesis, `cgroup.kill`, then rmdir, then kill-by-UID through pidfds, verified by an
  independent `/proc` scan. Any residue aborts the run.

## 3. Constants (fixed; calibrated in §7)

| constant | value | | constant | value |
|---|---|---|---|---|
| CHILDREN | 3 | | KILL_BOUND | 1.0 s |
| TREE_N | 8 | | REAP_BOUND | 5.0 s |
| END_AFTER | 0.8 s after READY | | FIRE_TOL | 0.25 s |
| EARLY_JOB / LATE_JOB | 0.3 s / 1.5 s | | SENTINEL_TOL | 1.0 s |
| H3_JOBS | 0.3, 0.6, 0.9 s | | POST_DUE | 0.7 s |
| LIFETIME | 20 s | | WALL_LIMIT | 115 s |

**Repetitions:** 5 per hypothesis.

## 4. Hypotheses (each must pass in all 5 repetitions)

- **H1 End-session leaves no process.**
  - Before the end, every live process of the session UID is in the session cgroup (independent `/proc` scan),
    with at least TREE_N processes.
  - After end-session: zero live processes within KILL_BOUND, and no `/proc` entry within REAP_BOUND.
  - A registration for the ended session is refused.
- **H2 No job fires after end-session.** Session B is active, and the agent claims it for its jobs.
  - Both jobs are registered under the caller's own session: the claim is ignored.
  - The early job fired during the session (non-vacuity).
  - No fire event of a session-A job at or after the end (scheduler log).
  - The job due after the end is `cancelled`.
  - No job sentinel was written at or after the end (job-side record).
- **H3 Usefulness.**
  - Three jobs registered during the session all fire.
  - Scheduler lateness ≤ FIRE_TOL.
  - Each job's own sentinel shows the session UID, the session cgroup, and a time ≤ SENTINEL_TOL after its due time.
  - The session then ends cleanly.
- **H4 Controls fire (NEGATIVE_CONTROL).** Each weakens exactly one check, and each must be DETECTED by the H1/H2
  observations:

| control | weakening | required detection |
|---|---|---|
| (a) | the scheduler honours the claimed session | a session-A job fires after A ended |
| (b) | the harness starts a session-UID helper without placement | the helper is alive after end-session |
| (c) | end-session kills only the top process | at least TREE_N − 1 descendants are alive |

## 5. Runs, re-runs and stopping

- **One evidence run:** `--kind evidence --reps 5 --out scenarios/SC-12/evidence/run-1`.
- **Infrastructure errors:** an INFRA-ERROR at preflight (no hypothesis ran) allows one further run, to `run-2`.
  Both are kept.
- **Failures:** a hypothesis failure is final for this ID.
- **Stop** on residue after any hypothesis, on the wall limit, or on any effect outside `sc12-test`, the run
  directory or the reserved UIDs.

## 6. What a result licenses

**Pass:** on this host, the session controller's lineage covers processes, a session-detached daemon and its own
scheduler's jobs; end-session leaves nothing alive and fires nothing later; each of the three Lean necessity
witnesses has a concrete runtime counterpart that the checks detect. This is CONDITIONAL. It is not a claim about
other creation paths, and it is not deployment assurance.

## 7. Dry-run calibration (before freezing)

| quantity | worst observed | bound |
|---|---|---|
| end-session kill latency | 0.049 s | KILL_BOUND 1.0 s |
| `/proc` entries gone | 0.049 s | REAP_BOUND 5.0 s |
| scheduler lateness | 0.005 s | FIRE_TOL 0.25 s |
| job sentinel after due time | 0.05–0.10 s | SENTINEL_TOL 1.0 s (tightened from 1.5 s) |

The dry runs (`sc12-dry1`, 1 rep; `sc12-dry2`, 5 reps, 60 s wall) passed every hypothesis and detected every
control. Every bound has at least a 10× margin over the observed maximum, chosen for a shared host.

## 8. Pinned artifacts (SHA-256 at freeze)

Commit: `065b57e47d47dcb548d686150cea11386ba3fc67`.

| Path | SHA-256 |
|---|---|
| `scenarios/SC-12/harness/cgctl.py` | `ba553bcd6f27b6cba84a6d7c7217f923073689ce2b9d960185810b91ec9ce1c2` |
| `scenarios/SC-12/harness/scheduler.py` | `d55a5843b15064487a0fc87fc8714de8f3e9d9d352b7e6334e85279084d52194` |
| `scenarios/SC-12/harness/workloads.py` | `ea6a721d808ffb94087fe466dc6a8885e3e9c3b6ef55b30e5ae5c4c546fc6bf6` |
| `scenarios/SC-12/harness/run_sc12.py` | `1a9b749aa3e1d29f40425e26711d268c4dc88e19dedea2a9512b44a4343567ba` |
| `ControlStack/Scenarios/SC12Persistence.lean` | `4930845d116ff03a68ec4d1995addcf45e42f9a95d21d4646ecfbadaac808cab` |
