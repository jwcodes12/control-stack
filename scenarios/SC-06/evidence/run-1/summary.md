# SC-06 shared artifacts (evidence, PREREG-SC06-ARTIFACTS-v1)

- commit: `fabf2ad36d29a7a3fddbec3d43b01867a0e7c3ae` (harness/prereg status: `clean`)
- calibration: FIXED, L_TASK = 0.3 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:28:18.560752Z, finished 2026-10-09T15:28:40.106858Z, wall 21.6 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: B context entries 60, defects 0
- H2 rep 1: user decisions [(120, True), (130, True), (140, True), (999, False)]
- H3 rep 1: latency ms {'p50': 23.7, 'max': 40.04}
- H4 rep 1: controls fired: {'a_raw_path': True, 'b_no_canonicalisation': True, 'c_no_provenance_check': True}
- H1 rep 2: B context entries 60, defects 0
- H2 rep 2: user decisions [(120, True), (130, True), (140, True), (999, False)]
- H3 rep 2: latency ms {'p50': 15.37, 'max': 24.3}
- H4 rep 2: controls fired: {'a_raw_path': True, 'b_no_canonicalisation': True, 'c_no_provenance_check': True}
- H1 rep 3: B context entries 60, defects 0
- H2 rep 3: user decisions [(120, True), (130, True), (140, True), (999, False)]
- H3 rep 3: latency ms {'p50': 28.5, 'max': 46.95}
- H4 rep 3: controls fired: {'a_raw_path': True, 'b_no_canonicalisation': True, 'c_no_provenance_check': True}
- H1 rep 4: B context entries 60, defects 0
- H2 rep 4: user decisions [(120, True), (130, True), (140, True), (999, False)]
- H3 rep 4: latency ms {'p50': 22.42, 'max': 32.46}
- H4 rep 4: controls fired: {'a_raw_path': True, 'b_no_canonicalisation': True, 'c_no_provenance_check': True}
- H1 rep 5: B context entries 60, defects 0
- H2 rep 5: user decisions [(120, True), (130, True), (140, True), (999, False)]
- H3 rep 5: latency ms {'p50': 24.59, 'max': 38.36}
- H4 rep 5: controls fired: {'a_raw_path': True, 'b_no_canonicalisation': True, 'c_no_provenance_check': True}

## Failed checks

none
