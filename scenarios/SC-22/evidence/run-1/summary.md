# SC-22 replication sampling (evidence, PREREG-SC22-REPL-v1)

- commit: `f4ab5d23c0b7bb62a3c0e72d82f31d2e221a55ca` (harness/prereg status: `clean`)
- calibration: FIXED, TRIALS = 2000 per configuration; seed `sc22-replication-evidence-v1`
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:02:54.319814Z, finished 2026-10-09T15:03:17.652893Z, wall 23.3 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: k=1: observed 0.9045, exact 0.9000, CI [0.8802, 0.9255]; k=3: observed 0.7480, exact 0.7265, CI [0.7138, 0.7802]; k=5: observed 0.5880, exact 0.5838, CI [0.5500, 0.6253]
- H2 rep 1: flagged 0 of 2000
- H3 rep 1: visible-sample survival {1: '2000/2000', 3: '2000/2000', 5: '2000/2000'}
- H1 rep 2: k=1: observed 0.9020, exact 0.9000, CI [0.8775, 0.9232]; k=3: observed 0.7340, exact 0.7265, CI [0.6992, 0.7669]; k=5: observed 0.5805, exact 0.5838, CI [0.5424, 0.6179]
- H2 rep 2: flagged 0 of 2000
- H3 rep 2: visible-sample survival {1: '2000/2000', 3: '2000/2000', 5: '2000/2000'}
- H1 rep 3: k=1: observed 0.8995, exact 0.9000, CI [0.8747, 0.9210]; k=3: observed 0.7295, exact 0.7265, CI [0.6946, 0.7626]; k=5: observed 0.5890, exact 0.5838, CI [0.5510, 0.6263]
- H2 rep 3: flagged 0 of 2000
- H3 rep 3: visible-sample survival {1: '2000/2000', 3: '2000/2000', 5: '2000/2000'}
- H1 rep 4: k=1: observed 0.9000, exact 0.9000, CI [0.8753, 0.9214]; k=3: observed 0.6950, exact 0.7265, CI [0.6590, 0.7294]; k=5: observed 0.5605, exact 0.5838, CI [0.5223, 0.5982]
- H2 rep 4: flagged 0 of 2000
- H3 rep 4: visible-sample survival {1: '2000/2000', 3: '2000/2000', 5: '2000/2000'}
- H1 rep 5: k=1: observed 0.9065, exact 0.9000, CI [0.8824, 0.9272]; k=3: observed 0.7255, exact 0.7265, CI [0.6904, 0.7587]; k=5: observed 0.5745, exact 0.5838, CI [0.5364, 0.6120]
- H2 rep 5: flagged 0 of 2000
- H3 rep 5: visible-sample survival {1: '2000/2000', 3: '2000/2000', 5: '2000/2000'}

## Failed checks

none
