# SC-12 harness: session lineage

A defensive, benign-workload runtime check of `SC12Persistence.sc12_safe` / `no_fire_after_end`. Preregistration:
[`prereg/SC12-LINEAGE.md`](../../../prereg/SC12-LINEAGE.md).

| file | role |
|---|---|
| `cgctl.py` | minimal cgroup-v2 controller with host-safety bounds; independent `/proc` observation. An identical copy is in SC-14. |
| `scheduler.py` | trusted session controller + job scheduler: jobs registered over a Unix socket (SO_PEERCRED selects the session), fired inside the session cgroup; end-session = refuse, cancel, `cgroup.kill` |
| `workloads.py` | benign agent tree with a session-detached daemon, the job (writes a sentinel), and the bypass helper |
| `run_sc12.py` | H1–H4 runner, receipts, preflight, cleanup and residue checks |
| `test_sc12.py` | no-root unit tests of the scheduler (fake cgroup layer) and the bounds |

**Host's own schedulers.** The host's cron, at and systemd timers are never touched.

**Cgroup and UID limits.** Cgroups only under `/sys/fs/cgroup/sc12-test`, UIDs 23901–23904. Limits are set before
any process enters.

```sh
python3 -m unittest discover -s scenarios/SC-12/harness -p 'test_*.py'
sudo -n /bin/python3 -B scenarios/SC-12/harness/run_sc12.py --kind dry --reps 1 --out /tmp/.../sc12-dryN
sudo -n /bin/python3 -B scenarios/SC-12/harness/run_sc12.py --cleanup-stale      # only after an aborted run
# evidence, after the prereg is frozen and committed:
sudo -n /bin/python3 -B scenarios/SC-12/harness/run_sc12.py --kind evidence --reps 5 --out scenarios/SC-12/evidence/run-1
```
