# Preregistration: SC-28 cgroup v2 meter, single-host reference run (v1)

**ID:** `PREREG-SC28-CGMETER-v1`. **Written:** 2026-10-09, before any dry run or evidence run.
**Freeze:** this file's Git commit and SHA-256 are recorded in every receipt. After the evidence run starts, this file
is not edited. A change needs a new ID (`-v2`), a new file and a new run. The earlier run is kept.

## 1. Claim under test and its scope

SC-28: several agents can each stay within their own limits and still jointly exceed an overall budget. The candidate
mitigation tested here is narrow and operational: a trusted job controller that

- places every job (a "lease") in its own cgroup v2 child of one run cgroup that carries the global cap;
- places each process in the lease cgroup **before exec**, while the launcher is still root, so everything the job
  later starts is accounted to it by the kernel;
- reads the kernel's accounting (`cpu.stat`, `pids.current`/`pids.peak`, `memory.peak`);
- stops a single job with `cgroup.kill` on its lease ("revoke");
- stops everything with `cgroup.freeze` then `cgroup.kill` on the run ("HALT"), and refuses launches afterwards.

The run asks whether this mechanism accounts for, caps and stops **benign** workloads, including one ordinary
daemon-style child started with `start_new_session=True`. That child is the case that escapes session- and
process-group-based job control.

**Model:** `ControlStack/Scenarios/SC28Budget.lean` (shared budget, trusted meter, global cap). This run does not
check the model against the runtime. It checks only the operational mechanism the model assumes: a meter that sees
every unit of consumption and a cap enforced on the sum.

**Implementation:** `scenarios/SC-28/harness/`. It has three parts:
- the controller (`meter.py`);
- the benign workloads (`workloads.py`);
- the checks and the receipt (`run_sc28.py`).

**Not tested here, and not claimed:**
- **Resistance to an adversarial workload.** No workload tries to escape its cgroup, ignore signals, fork-bomb,
  retry forks, attack the controller or race the kill. This run checks the accounting and termination mechanism
  only.
- **Other hosts.** Generalisation to other hosts, kernels, or to cgroup v1.
- **Trust in root.** Compromise of root, of the kernel, or of the controller.
- **Other resources.** GPU time and other accelerators; network or disk I/O budgets; spend in money or API tokens.
  CPU here means CPU time only.
- **Memory caps.** The memory cap is set and recorded, but not tested.
- **Several controllers.** Several controllers, or several hosts sharing one budget.
- **Persistence.** Persistence across reboots or controller restarts.
- **Kernel-side refusal.** Refusal after revoke or HALT is the controller's own state check. The kernel does not
  enforce it.

## 2. Environment and trust

- **Host:** the OCI ARM64 Linux box running this repository (single host, shared with other work).
- **cgroup v2:** at `/sys/fs/cgroup`, with `cpu`, `memory` and `pids` enabled in the root's `cgroup.subtree_control`.
  The controller needs `cgroup.kill` (Linux ≥ 5.14) and `cgroup.freeze` (≥ 5.2).
- **Separate numeric UIDs:** lease A 23701, lease B 23702, the H5 unplaced control 23709. The range 23700–23709 is
  reserved: the controller refuses any other UID, and the run aborts before any test if any process already runs
  under one of them. No accounts are created; the UIDs are set with `setgroups([])`, `setgid` and `setuid` in the
  forked child.
- **Trusted:** the Linux kernel, the root controller and runner at the recorded hashes, and CPython.
- **Untrusted:** nothing in the adversarial sense. The workloads are benign by construction (§1).
- **Receipt contents:**
  - the Git commit and dirty status, and the SHA-256 of every harness file and of this file;
  - `uname -r` and `uname -a`;
  - the Python version, and the controller's own cgroup;
  - the load average at start and end;
  - every cgroup's limits, read back after writing;
  - the raw measurements, and expected vs observed for every check.

**Host-safety bounds** are enforced in `meter.py` and are part of this registration:
- **Location:** cgroups exist only under `/sys/fs/cgroup/sc28-test`.
- **Limits:** every test cgroup (top, run, lease) gets its limits written and read back before any process enters
  it:
  - `cpu.max` quota ≤ 50000 per 100000 period;
  - `pids.max` ≤ 64;
  - `memory.max` ≤ 128 MiB.
- **Self-exit:** every workload process exits by itself after 30 s.
- **Wall limit:** a run has a 115 s limit.
- **Cleanup always runs**, in `finally` blocks: `cgroup.kill`, then wait until `cgroup.procs` is empty, then remove
  the children and then the parent. After every hypothesis the runner checks that no reserved-UID process and no
  run cgroup is left.

## 3. Hypotheses and decision rules

**Workload tree** (used by H1, H3, H4 and H5): one parent; 8 children; 2 grandchildren per child; one daemon child
with its own session (`start_new_session=True`, stdio detached). That is 26 processes. All of them sleep, except
where a hypothesis gives some children a bounded CPU loop (2–3 s of integer arithmetic). Each tree prints one
`READY` line with its own pid report once all 26 processes exist.

**"Live"** means a `/proc/<pid>` entry whose real UID is the workload UID and whose state is not `Z` or `X`.

**The /proc scan** is independent of the controller: it reads only `/proc/<pid>/status`, `stat` and `cgroup`, and
never a cgroup file.

**Pass rule:** each hypothesis runs **5 repetitions**, each on freshly created cgroups. A hypothesis passes only if
every check passes in all 5 repetitions. An exception inside a repetition fails it.

**H1 Attribution.** Lease A (`pids.max` 32) runs the tree with 2 CPU children. After `READY`:
- the tree is complete (26 pids reported);
- lease A's `cgroup.procs` equals, as a set, the live /proc scan of UID 23701;
- lease A's `cgroup.procs` equals, as a set, the workload's own pid report;
- the daemon's session id equals its own pid and differs from the parent's session id (it really is
  session-detached);
- the daemon's pid is in lease A's `cgroup.procs`;
- `/proc/<pid>/cgroup` of every live UID-23701 process is exactly lease A's path;
- lease A's `pids.current` = 26.

**H2 Joint cap.**
- **(a) CPU.** The run has `cpu.max` 50000 100000 (0.50 CPU). Leases A and B each have `cpu.max` 50000 100000.
  - **Setup:** each lease runs one CPU loop of 3.5 s wall time. After both `READY` lines and 0.3 s of warm-up,
    `usage_usec` of A, B and the run is sampled at the start and end of a 2.0 s window.
  - **Pass condition 1:** the sum of the lease quotas (100000) exceeds the run quota (50000). This is a
    configuration check that the leases individually allow more than the joint cap.
  - **Pass condition 2:** the combined rate (ΔA + ΔB) / Δt ≤ **0.55 CPU**, that is, cap 0.50 plus tolerance
    **0.05**.
  - **Pass condition 3:** the run-cgroup rate is ≤ 0.55 CPU.
  - **Pass condition 4:** the run's `cpu.stat nr_throttled` rose by ≥ 1 within the window. This shows the cap was
    binding, so condition 2 is not met merely because demand was low.
  - **Why 0.05:** CFS bandwidth control refills the quota each 100 ms period. A window that is not aligned with the
    periods can include at most about one extra period's quota (0.05 CPU-s over 2.0 s = 0.025 CPU), plus per-CPU
    runtime slices. 0.05 covers both, with margin, and is 10% of the cap.
- **(b1) pids, single lease.** The run and lease A both have `pids.max` 8. Lease A runs a workload that tries
  exactly 12 forks, once each, with no retry.
  - 7 forks succeed;
  - 5 forks fail with `EAGAIN`;
  - there are no other errors;
  - lease A's `pids.current` = 8;
  - `pids.peak` ≤ 8, when the kernel exposes it.
- **(b2) pids, joint.** The run has `pids.max` 8; leases A and B have `pids.max` 8 each. A runs a holder (1 parent
  + 3 children = 4 pids). Then B tries exactly 12 forks.
  - A's `pids.current` = 4;
  - B gets 3 successes and 9 `EAGAIN`, with no other errors. B's own limit would have allowed 7, so these numbers
    show the run's cap binding;
  - the run's `pids.current` = 8;
  - the run's `pids.peak` ≤ 8, when exposed.

**H3 Revocation.** Leases A (UID 23701) and B (UID 23702) each run the full tree (A with 1 CPU child).
- **Precondition:** each lease's `cgroup.procs` equals its tree report (26).
- **Action:** revoke A.
- **Pass, termination:** both of the following hold within **1.0 s** of the `cgroup.kill` write:
  - zero live UID-23701 processes (/proc scan);
  - lease A's `cgroup.procs` is empty.
- **Pass, reaping:** no UID-23701 `/proc` entry at all, zombies included, within **5.0 s**.
- **Pass, isolation:** lease B's `cgroup.procs` is unchanged and equals the live UID-23702 set.
- **Pass, refusal:** a later launch into A raises `Refused`, and a /proc scan 0.3 s later finds no UID-23701 process.

**H4 HALT.** Leases A and B run the full tree (B with 2 CPU children running a 3 s loop).
- **Precondition:** 52 live workload-UID processes.
- **Action:** HALT, which is `cgroup.freeze` = 1 on the run, then `cgroup.kill` = 1. Latency is measured from just
  before the freeze write.
- **Pass, freeze:** `cgroup.events` shows `frozen 1` within 0.5 s, before the kill.
- **Pass, termination:** zero live UID-23701/23702 processes, and both leases' `cgroup.procs` empty, within
  **1.0 s**.
- **Pass, reaping:** no such `/proc` entry at all, zombies included, within **5.0 s**.
- **Pass, run state:** the run's `cgroup.events populated` = 0.
- **Pass, refusal:** all three of the following raise `Refused`:
  - a launch into A;
  - a launch into B;
  - creating a new lease.

  In addition, a /proc scan 0.3 s later finds no workload-UID process.

**H5 Control: placement is required.** A run with lease L (`pids.max` 32).
- **Setup, unplaced tree:** the same tree, all sleeping, with the daemon, is launched under UID 23709 by the same
  credential drop but **without** cgroup placement.
- **Pass, unplaced tree:** all of the following hold:
  - the /proc scan shows the 26 reported pids live;
  - lease L's `cgroup.procs` contains none of them, and L's `pids.current` = 0;
  - the run's `pids.current` = 0;
  - none of the 26 processes has a cgroup path under `/sc28-test`.
- **Setup, placed tree:** the same tree is then launched into L through the controller (UID 23701).
- **Pass, placed tree:** L's `cgroup.procs` equals both the live UID-23701 scan and that tree's report.
- **Cleanup by UID:** the unplaced tree is cleaned up by SIGKILL, using pidfds, to every live UID-23709 process.
  This repeats until 3 consecutive scans are empty. Pass: no UID-23709 `/proc` entry within 5.0 s.

  This shows why the mechanism needs launch-time placement by the trusted controller. Work started outside it is
  invisible to the meter and to the caps.

**Overall pass:** H1–H5 all pass, the run is not aborted, and the final cleanup leaves no reserved-UID process and no
`/sys/fs/cgroup/sc28-test`.

## 4. Runs, re-runs and stopping

- **Dry runs:** use `--kind dry` and go to scratch directories. They are for debugging and are not evidence.
- **The evidence run** is exactly one invocation of:
  ```
  sudo -n /bin/python3 scenarios/SC-28/harness/run_sc28.py --kind evidence --reps 5 --out <new dir>
  ```
  - It runs from a commit in which this file and every harness file are committed and unmodified. The runner refuses
    otherwise.
  - It runs all five hypotheses.
  - The receipt directory is kept, whatever the outcome.
- **Infrastructure errors:** a re-run is allowed only for an infrastructure error, defined as a preflight failure
  before any hypothesis starts:
  - not root;
  - cgroup v2 or the controllers unavailable;
  - a stale `sc28-test`;
  - a reserved-UID process already running;
  - a dirty tree.

  At most one re-run, and both receipts are kept.
- **Failures are final:** a hypothesis failure, including one caused by load on the shared host, is recorded as
  FAILED in the scenario manifest. It is never re-run under this ID. A re-run with changed bounds needs `-v2`.
- **Stop:** the runner aborts the whole run, with cleanup, if any of the following happens:
  - a reserved-UID process or a run cgroup survives a hypothesis;
  - the 115 s wall limit is reached;
  - cleanup cannot empty a cgroup within 5 s.

## 5. What a pass licenses

A pass licenses only this statement. On this host and kernel, a root controller that places each job's first process
into a lease cgroup before exec does all of the following for benign workloads:
- it accounts every descendant, including a session-detached daemon, to that lease;
- it enforces a CPU-time and pids cap on the sum of leases;
- it stops one lease, or the whole run, within 1 s.

Without placement, the same work is invisible to the meter.

A pass is an operational premise for the SC-28 trusted-meter assumption. It is not evidence about adversarial
workloads or other resources (GPU, money, tokens), and it does not move SC-28 out of DRAFT on its own. Independent
review (RUNTIME-VM-HANDOFF.md §10) remains open.
