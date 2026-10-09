# SC-10/11 harness: policy store, enforcement point and pinned toolchain

This is a defensive reference test on one Linux host. Three trusted services:
- **Policy store:** keeps an append-only versioned log. Each version records the writer (pid via SO_PEERCRED), the
  digest and a commit stamp. Only the admin, the runner's pid, may write.
- **Enforcement point:** an egress-decision service that reads the **latest** version on every decision (no cache)
  and logs the version it used.
- **Build service:** runs the toolchain from a **pinned absolute path** after checking its digest, whatever PATH the
  caller supplies.

The agent's writes come from separate client processes. Identity here is the process pid under one UID; credential
separation is a premise, not tested.

The preregistration is [`prereg/SC10-POLICY-STORE.md`](../../../prereg/SC10-POLICY-STORE.md)
(`PREREG-SC10-POLICY-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC10Policy.lean`.

## Files

| file | role |
|---|---|
| `store.py` | The append-only policy log (fsync, then a commit stamp), admin-only writes, and an atomic `latest`. Control: `--any-writer`. |
| `pep.py` | The egress-decision service: reads the latest version per decision and logs version, length and the moment applied. Controls: `--cache-ttl`, `--alt-file`. |
| `builder.py` | The pinned toolchain: it hashes the pinned file, checks the digest and runs exactly those bytes. Control: `--path-resolve`. |
| `client.py` | A one-shot client, used for the agent's write attempts from a separate process. |
| `reconcile.py` | Decisions checked against the store's own log on the shared monotonic clock; builds checked against the pinned digest. It also has mutation self-tests. |
| `run_sc10.py` | The flows, the H1–H6 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | decisions while the admin writes v1 and v2 | each decision used the latest admin version at that moment | `sc10_safe`, `policy_admin_only` |
| H2 | the agent writes a policy | refused; no effect | `agent_writable_policy_breaks` (deployed half) |
| H3 | tighten, then decide | no decision after the tightening uses the old version | `stale_cache_breaks` (deployed half) |
| H4 | the agent prepends a same-named toolchain to PATH | the pinned toolchain always runs; a wrong pinned digest is refused | `path_toolchain_breaks` (deployed half) |
| H5 | 100 decisions, 5 builds | within L_DEC | usefulness |
| H6 | **NEGATIVE_CONTROL**: agent-writable store, cached policy, alternate evaluator, PATH toolchain | each detected; the stale window is measured | the four `…_breaks` witnesses |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-10/harness/run_sc10.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-10/harness/run_sc10.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc10-run-*` directory (mode 0700). That directory is removed at the end.
- **Effects:** egress "decisions" are answers about strings, and the "toolchain" only writes its own digest to an
  output file.
- **Wall limit:** each run has a 115 s limit.
