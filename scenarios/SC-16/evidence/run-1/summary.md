# SC-16 deploy admission (evidence, PREREG-SC16-ADMIT-v1)

- commit: `6ee5e21b3922605cac8a14c02b51424713df8567` (harness/prereg status: `clean`)
- calibration: FIXED, L_DEP = 0.4 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T06:49:49.351263Z, finished 2026-10-09T06:50:27.330587Z, wall 38.0 s
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

- H1 rep 1: deployed files 8
- H2 rep 1: deployed files 3
- H3 rep 1: deployed files 3
- H4 rep 1: latency ms {'p50': 72.02, 'p95': 78.68, 'max': 79.78}
- H5 rep 1: deployed files 2
- H6 rep 1: controls fired: {'a_deploy_by_tag': True, 'b_no_target_binding': True, 'c_self_review': True, 'd_no_nonce': True}
- H1 rep 2: deployed files 8
- H2 rep 2: deployed files 3
- H3 rep 2: deployed files 3
- H4 rep 2: latency ms {'p50': 71.38, 'p95': 77.55, 'max': 82.57}
- H5 rep 2: deployed files 2
- H6 rep 2: controls fired: {'a_deploy_by_tag': True, 'b_no_target_binding': True, 'c_self_review': True, 'd_no_nonce': True}
- H1 rep 3: deployed files 8
- H2 rep 3: deployed files 3
- H3 rep 3: deployed files 3
- H4 rep 3: latency ms {'p50': 76.82, 'p95': 91.76, 'max': 103.46}
- H5 rep 3: deployed files 2
- H6 rep 3: controls fired: {'a_deploy_by_tag': True, 'b_no_target_binding': True, 'c_self_review': True, 'd_no_nonce': True}
- H1 rep 4: deployed files 8
- H2 rep 4: deployed files 3
- H3 rep 4: deployed files 3
- H4 rep 4: latency ms {'p50': 78.61, 'p95': 93.34, 'max': 119.87}
- H5 rep 4: deployed files 2
- H6 rep 4: controls fired: {'a_deploy_by_tag': True, 'b_no_target_binding': True, 'c_self_review': True, 'd_no_nonce': True}
- H1 rep 5: deployed files 8
- H2 rep 5: deployed files 3
- H3 rep 5: deployed files 3
- H4 rep 5: latency ms {'p50': 77.59, 'p95': 86.02, 'max': 93.53}
- H5 rep 5: deployed files 2
- H6 rep 5: controls fired: {'a_deploy_by_tag': True, 'b_no_target_binding': True, 'c_self_review': True, 'd_no_nonce': True}

## Failed checks

none
