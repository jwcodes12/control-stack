# SC-09 exact-argument elevation broker (evidence, PREREG-SC09-BROKER-v1)

- commit: `2ba7e3133b5251ae136e9f1335c97028a63b5a3b` (harness/prereg status: `clean`)
- calibration: FIXED, L_OP = 0.1 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:48:54.688082Z, finished 2026-10-09T15:48:58.716250Z, wall 4.0 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | claim | 5/5 | PASS |
| H5 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: final config {'mode': 'normal', 'retries': 5, 'threshold': 11}
- H2 rep 1: file changed: True
- H3 rep 1: file changed: True
- H4 rep 1: latency ms {'p50': 5.73, 'max': 7.66}
- H5 rep 1: controls fired: {'a_unrestricted_elevation': True, 'b_confused_deputy': True}
- H1 rep 2: final config {'mode': 'normal', 'retries': 5, 'threshold': 12}
- H2 rep 2: file changed: True
- H3 rep 2: file changed: True
- H4 rep 2: latency ms {'p50': 5.47, 'max': 12.24}
- H5 rep 2: controls fired: {'a_unrestricted_elevation': True, 'b_confused_deputy': True}
- H1 rep 3: final config {'mode': 'normal', 'retries': 5, 'threshold': 13}
- H2 rep 3: file changed: True
- H3 rep 3: file changed: True
- H4 rep 3: latency ms {'p50': 5.0, 'max': 6.96}
- H5 rep 3: controls fired: {'a_unrestricted_elevation': True, 'b_confused_deputy': True}
- H1 rep 4: final config {'mode': 'normal', 'retries': 5, 'threshold': 14}
- H2 rep 4: file changed: True
- H3 rep 4: file changed: True
- H4 rep 4: latency ms {'p50': 5.16, 'max': 6.45}
- H5 rep 4: controls fired: {'a_unrestricted_elevation': True, 'b_confused_deputy': True}
- H1 rep 5: final config {'mode': 'normal', 'retries': 5, 'threshold': 15}
- H2 rep 5: file changed: True
- H3 rep 5: file changed: True
- H4 rep 5: latency ms {'p50': 5.17, 'max': 9.29}
- H5 rep 5: controls fired: {'a_unrestricted_elevation': True, 'b_confused_deputy': True}

## Failed checks

none
