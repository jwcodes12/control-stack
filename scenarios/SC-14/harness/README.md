# SC-14 harness: per-job multi-resource budgets

A defensive, benign-workload runtime check of `SC14Runaway.sc14_safe` for CPU time, memory, pids, CPU rate and lease
expiry. Preregistration: [`prereg/SC14-MULTI-RESOURCE.md`](../../../prereg/SC14-MULTI-RESOURCE.md).

**Network egress is not covered here.** SC-07 covers byte quotas.

| file | role |
|---|---|
| `cgctl.py` | identical copy of the SC-12 controller (host-safety bounds, `/proc` observation) |
| `jobs.py` | trusted per-job controller: kernel caps (memory with swap off, pids, `cpu.max`); 10 ms meter for the CPU-time budget and the expiry, both enforced by `cgroup.kill`; an aggregate-only mode for the control |
| `workloads.py` | benign bounded workloads: CPU loop, allocation, forks, a within-budget job, sleep |
| `run_sc14.py` | H1–H5 runner, receipts, preflight, cleanup and residue checks |
| `test_sc14.py` | no-root unit tests of the controller (fake cgroup files) |

```sh
python3 -m unittest discover -s scenarios/SC-14/harness -p 'test_*.py'
sudo -n /bin/python3 -B scenarios/SC-14/harness/run_sc14.py --kind dry --reps 1 --out /tmp/.../sc14-dryN
# evidence, after the prereg is frozen and committed:
sudo -n /bin/python3 -B scenarios/SC-14/harness/run_sc14.py --kind evidence --reps 5 --out scenarios/SC-14/evidence/run-1
```
