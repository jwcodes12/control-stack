# SC-09 harness: exact-argument elevation broker (unprivileged)

This is a defensive reference test on one Linux host. The broker and the requesters are ordinary processes under one
UID. The broker owns a protected JSON config file in its private 0700 directory inside the run dir and applies only
preregistered (rule, exact-argument) changes to it. A requester never gets a handle to the file. The broker
identifies a caller by the kernel-reported pid (SO_PEERCRED).

**Scope.** This tests the exact-argument rule check and the refusal to trust a claimed caller field. It does **not**
test UID-level or kernel privilege separation: no sudo, no numeric UIDs, no setuid. That the kernel enforces the
separation is a premise, stated in the prereg.

The preregistration is [`prereg/SC09-ELEVATION-BROKER.md`](../../../prereg/SC09-ELEVATION-BROKER.md)
(`PREREG-SC09-BROKER-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC09Priv.lean`.

## Files

| file | role |
|---|---|
| `broker.py` | Owns the protected file; applies only rules with an in-range/enum argument, invoked by the authorised requester (by peer pid); keeps an fsync'd diff log and a file hash chain. Controls: `--no-arg-check`, `--trust-claimed`. |
| `requester.py` | A requester process with a stable pid; forwards requests, never opens the file. |
| `reconcile.py` | Replays the broker's diff log against the file, independently of the broker's rule code, with mutation self-tests. |
| `run_sc09.py` | The flows, the H1-H5 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | in-rule, guest, out-of-range, bad-enum requests | only the in-rule ops requests apply | `sc09_safe` |
| H2 | non-matching arguments | all refused; file unchanged | `sc09_safe` |
| H3 | guest claims `as: ops` | refused (peer identity used) | `confused_deputy_breaks` (deployed half) |
| H4 | 30 in-rule requests | all apply within L_OP | usefulness |
| H5 | **NEGATIVE_CONTROL**: no argument check; trust claimed caller | arbitrary content written / guest writes as ops; each detected | `unrestricted_elevation_breaks`, `confused_deputy_breaks` |

## Run

No root is needed, and the runner refuses to run as root. No sudo, no numeric UIDs.

```
/bin/python3 -B scenarios/SC-09/harness/run_sc09.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-09/harness/run_sc09.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, no accounts, no sudo, no numeric UIDs, no TCP. Only Unix sockets
  (mode 0600) in a fresh `/var/tmp/sc09-run-*` directory (mode 0700), removed at the end. No system file is touched.
- **Resource:** the protected file is a small JSON config of benign numbers and enum strings inside the run dir.
- **Wall limit:** 115 s. A full run takes a few seconds.
