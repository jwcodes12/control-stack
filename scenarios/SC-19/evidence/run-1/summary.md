# SC-19 two-phase destructive operations (evidence, PREREG-SC19-TWOPHASE-v1)

- commit: `d5427dba83c85cb29b256cd7caa5f547458dafe5` (harness/prereg status: `clean`)
- calibration: FIXED, L_OP = 0.7 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T07:06:17.152008Z, finished 2026-10-09T07:06:54.418512Z, wall 37.3 s
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

- H1 rep 1: destroys 6
- H2 rep 1: destroys 3
- H3 rep 1: destroys 0
- H4 rep 1: drills [(5, True), (6, True), (7, True)]
- H5 rep 1: latency ms {'p50': 156.29, 'max': 242.44}, background writes 103
- H6 rep 1: controls fired: {'a_stale_snapshot': True, 'b_unverified_snapshot': True, 'c_prepare_time_count': True}
- H1 rep 2: destroys 6
- H2 rep 2: destroys 3
- H3 rep 2: destroys 0
- H4 rep 2: drills [(5, True), (6, True), (7, True)]
- H5 rep 2: latency ms {'p50': 118.09, 'max': 165.42}, background writes 72
- H6 rep 2: controls fired: {'a_stale_snapshot': True, 'b_unverified_snapshot': True, 'c_prepare_time_count': True}
- H1 rep 3: destroys 6
- H2 rep 3: destroys 3
- H3 rep 3: destroys 0
- H4 rep 3: drills [(5, True), (6, True), (7, True)]
- H5 rep 3: latency ms {'p50': 83.83, 'max': 116.98}, background writes 61
- H6 rep 3: controls fired: {'a_stale_snapshot': True, 'b_unverified_snapshot': True, 'c_prepare_time_count': True}
- H1 rep 4: destroys 6
- H2 rep 4: destroys 3
- H3 rep 4: destroys 0
- H4 rep 4: drills [(5, True), (6, True), (7, True)]
- H5 rep 4: latency ms {'p50': 68.84, 'max': 157.64}, background writes 59
- H6 rep 4: controls fired: {'a_stale_snapshot': True, 'b_unverified_snapshot': True, 'c_prepare_time_count': True}
- H1 rep 5: destroys 6
- H2 rep 5: destroys 3
- H3 rep 5: destroys 0
- H4 rep 5: drills [(5, True), (6, True), (7, True)]
- H5 rep 5: latency ms {'p50': 133.44, 'max': 247.33}, background writes 84
- H6 rep 5: controls fired: {'a_stale_snapshot': True, 'b_unverified_snapshot': True, 'c_prepare_time_count': True}

## Failed checks

none
