# SC-04 harness: log canonicaliser

This is a defensive reference test on one Linux host. A benign agent emits diagnostic log records; a trusted
canonicaliser maps each to one of K = 8 templates with f = 2 numeric fields quantised to Q = 4 levels and drops
everything else, including free text; the receiver sees only canonical records.

The proved per-record capacity is log2(K*Q^f) bits, and over m records recovery of a uniform secret is at most
(K*Q^f)^m / |M| (`ChannelInstances.log_channel`). A free-text field that is not canonicalised leaks a secret in one
record (`free_text_leaks`).

The preregistration is [`prereg/SC04-LOG-CANON.md`](../../../prereg/SC04-LOG-CANON.md) (`PREREG-SC04-LOGCANON-v1`). It
holds the decision rules, the fixed token count, the re-run policy and the mapping to `ChannelInstances.lean`.

## Files

| file | role |
|---|---|
| `canon.py` | The canonicaliser: template id plus f quantised fields, everything else dropped. Control: `--free-field`. |
| `agent.py` | The benign agent. Its covert emitter packs bits of a random benign token into the template and fields (disjoint bit slices) and also into free text, which is dropped. |
| `analyse.py` | The schema check, the empirical capacity (distinct views and a maximum-likelihood decoder vs the proved bound), and the leak check. |
| `run_sc04.py` | The flows, the H1-H4 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | 40 records with free text | the receiver's view is schema-only; no token leaks | `log_channel` premise |
| H2 | 2000 covert attempts, m in {1,2} | best-decoder accuracy <= (K*Q^f)^m/\|M\| | `log_channel` |
| H3 | 100 random records | per-template counts match the raw counts | usefulness |
| H4 | **NEGATIVE_CONTROL**: free-text passthrough | the token is recovered in one record | `free_text_leaks` |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-04/harness/run_sc04.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-04/harness/run_sc04.py --kind evidence --reps 5 --out /path/to/new-dir
```

## Host safety

- **Privileges and network:** unprivileged, no accounts, no sudo, no TCP. Only Unix sockets (mode 0600) in a fresh
  `/var/tmp/sc04-run-*` directory (mode 0700), removed at the end.
- **Data:** benign diagnostic text and random hex tokens.
- **Wall limit:** 115 s. A full run takes about 30 s.
