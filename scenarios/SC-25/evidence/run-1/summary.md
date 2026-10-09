# SC-25 audit-before-execute queue (evidence, PREREG-SC25-AUDITQ-v1)

- commit: `19c31b2e4ec162198ae9e65991b1718fd37c078e` (harness/prereg status: `clean`)
- calibration: FIXED, TAU_X = 0.1 s, L_USE = 0.3 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T06:32:17.955768Z, finished 2026-10-09T06:32:47.739736Z, wall 29.8 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | claim | 5/5 | PASS |
| H5 | claim | 5/5 | PASS |
| H6 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: effects 25
- H2 rep 1: effects 5
- H3 rep 1: max expiry lateness 0.0137 s
- H4 rep 1: latency ms {'p50': 34.24, 'p95': 62.31, 'p99': 71.73, 'max': 76.95}, executed 100
- H5 rep 1: executed before halt 39, after []
- H6 rep 1: controls fired: {'a_fail_open_timeout': True, 'b_digest_unchecked': True, 'c_nonatomic': True, 'd_const_digest': True, 'e_agent_class': True}
- H1 rep 2: effects 25
- H2 rep 2: effects 5
- H3 rep 2: max expiry lateness 0.0318 s
- H4 rep 2: latency ms {'p50': 31.92, 'p95': 50.48, 'p99': 62.64, 'max': 76.48}, executed 100
- H5 rep 2: executed before halt 57, after []
- H6 rep 2: controls fired: {'a_fail_open_timeout': True, 'b_digest_unchecked': True, 'c_nonatomic': True, 'd_const_digest': True, 'e_agent_class': True}
- H1 rep 3: effects 25
- H2 rep 3: effects 5
- H3 rep 3: max expiry lateness 0.0242 s
- H4 rep 3: latency ms {'p50': 40.71, 'p95': 73.22, 'p99': 77.29, 'max': 83.59}, executed 100
- H5 rep 3: executed before halt 69, after []
- H6 rep 3: controls fired: {'a_fail_open_timeout': True, 'b_digest_unchecked': True, 'c_nonatomic': True, 'd_const_digest': True, 'e_agent_class': True}
- H1 rep 4: effects 25
- H2 rep 4: effects 5
- H3 rep 4: max expiry lateness 0.0151 s
- H4 rep 4: latency ms {'p50': 35.73, 'p95': 63.8, 'p99': 78.49, 'max': 90.81}, executed 100
- H5 rep 4: executed before halt 72, after []
- H6 rep 4: controls fired: {'a_fail_open_timeout': True, 'b_digest_unchecked': True, 'c_nonatomic': True, 'd_const_digest': True, 'e_agent_class': True}
- H1 rep 5: effects 25
- H2 rep 5: effects 5
- H3 rep 5: max expiry lateness 0.0109 s
- H4 rep 5: latency ms {'p50': 29.56, 'p95': 54.99, 'p99': 65.51, 'max': 66.45}, executed 100
- H5 rep 5: executed before halt 52, after []
- H6 rep 5: controls fired: {'a_fail_open_timeout': True, 'b_digest_unchecked': True, 'c_nonatomic': True, 'd_const_digest': True, 'e_agent_class': True}

## Failed checks

none
