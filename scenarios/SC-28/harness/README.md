# SC-28 harness: cgroup v2 meter check

This is a defensive operational test. It asks whether a trusted job controller accounts for every process of a job.
It also asks whether "cancel job" (revoke one lease) and HALT (stop the whole run) stop all of those processes.

The workloads are benign and bounded: sleepers, a 2–3.5 s arithmetic loop, a small tree and one ordinary daemon
child. This harness checks the accounting and termination mechanism. It does not test resistance to an adversarial
workload.

The preregistration is [`prereg/SC28-CGROUP-METER.md`](../../../prereg/SC28-CGROUP-METER.md)
(`PREREG-SC28-CGMETER-v1`). It holds the decision rules, the tolerances and the re-run policy.

## Files

| file | role |
|---|---|
| `meter.py` | The trusted controller (root). It creates a run cgroup with a global cap and one child cgroup per lease. Limits are written and read back before any process enters. It launches with placement before exec: fork, then the child writes its own pid to the lease's `cgroup.procs`, verifies the placement, calls `setgroups`/`setgid`/`setuid`, and execs. It reads `cpu.stat`, `pids.*`, `memory.*` and `cgroup.events`. Revoke writes `cgroup.kill` on the lease. HALT writes `cgroup.freeze` then `cgroup.kill` on the run. After revoke or HALT, the controller refuses launches. |
| `workloads.py` | Benign workloads: `tree` (≤ 8 children × ≤ 2 grandchildren, plus an optional `start_new_session` daemon), `cpu` (bounded loop), `forks` (n single fork attempts, no retry) and `daemon`. Every process exits by itself after `--lifetime` (30 s). |
| `run_sc28.py` | H1–H5, an independent `/proc` scan, kill-by-UID through pidfds for the H5 control, and the receipt. |

## Run

Root is required. The runner uses the system Python 3.9 through sudo.

```
# dry run (debugging, not evidence); --only H1,H3 and --reps N are allowed
sudo -n /bin/python3 scenarios/SC-28/harness/run_sc28.py --kind dry --reps 5 --out /path/to/new-dir

# the single preregistered evidence run (needs committed, unmodified harness + prereg)
sudo -n /bin/python3 scenarios/SC-28/harness/run_sc28.py --kind evidence --reps 5 --out /path/to/new-dir

# recovery only: kill reserved-UID processes and remove a stale /sys/fs/cgroup/sc28-test
sudo -n /bin/python3 scenarios/SC-28/harness/run_sc28.py --kind dry --out /unused --cleanup-stale
```

The runner refuses an `--out` that already exists. The receipt holds:
- `meta.json`: the commit, dirty status, file SHA-256s, `uname`, the Python version, load averages, the top cgroup's
  settings and the constants;
- `results.jsonl`: one line per hypothesis × repetition, with the checks as expected / observed / pass and the raw
  measurements, including every cgroup's read-back limits;
- `verdicts.json`;
- `cleanup.json`;
- `summary.md`;
- `logs/`: workload stderr.

The receipt is chowned to `SUDO_UID`. The exit status is 0 only for an overall PASS.

## Host safety

The runner is built for a shared box:
- **Location:** cgroups are created only under `/sys/fs/cgroup/sc28-test`. `meter.py` refuses any other path.
- **Limits:** every cgroup gets `cpu.max` ≤ 50000/100000, `pids.max` ≤ 64 and `memory.max` ≤ 128 MiB before any
  process enters it.
- **UIDs:** workload UIDs are restricted to 23700–23709. The run refuses to start if any process already runs under
  one of them.
- **Cleanup:** cleanup runs in `finally` blocks: `cgroup.kill`, then wait until `cgroup.procs` is empty, then
  `rmdir` the children and then the parent. After each hypothesis, any leftover process or cgroup aborts the run.
  Then comes a final kill-by-UID and the removal of `sc28-test`.
- **Wall limit:** there is a 115 s wall limit (SIGALRM), and every workload exits by itself after 30 s.
- **The H5 unplaced tree:** it runs, by design, outside any test cgroup, in the controller's own cgroup. It is
  therefore all-sleeping: 26 processes, no CPU loop. It lives for about a second before it is killed by UID.
- **Isolation:** no account creation and no network. Files are written only to a temporary
  `/var/tmp/sc28-run-*`, which is removed afterwards, and to `--out`.
