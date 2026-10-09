# SC-15 merge gate (evidence, PREREG-SC15-MERGE-v1)

- commit: `9cc79d7605eaa6836e0e6fa61a7eecda91b5a74e` (harness/prereg status: `clean`)
- calibration: FIXED, L_MERGE = 2.15 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T07:27:03.877336Z, finished 2026-10-09T07:27:54.438851Z, wall 50.6 s
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

- H1 rep 1: commits on main 6
- H2 rep 1: commits on main 2
- H3 rep 1: commits on main 2
- H4 rep 1: latency ms {'p50': 173.2, 'max': 192.7}
- H5 rep 1: commits on main 2
- H6 rep 1: controls fired: {'a_stale_review': True, 'b_declared_paths': True, 'c_ci_other_content': True, 'd_self_review': True}
- H1 rep 2: commits on main 6
- H2 rep 2: commits on main 2
- H3 rep 2: commits on main 2
- H4 rep 2: latency ms {'p50': 169.7, 'max': 218.0}
- H5 rep 2: commits on main 2
- H6 rep 2: controls fired: {'a_stale_review': True, 'b_declared_paths': True, 'c_ci_other_content': True, 'd_self_review': True}
- H1 rep 3: commits on main 6
- H2 rep 3: commits on main 2
- H3 rep 3: commits on main 2
- H4 rep 3: latency ms {'p50': 186.9, 'max': 206.3}
- H5 rep 3: commits on main 2
- H6 rep 3: controls fired: {'a_stale_review': True, 'b_declared_paths': True, 'c_ci_other_content': True, 'd_self_review': True}
- H1 rep 4: commits on main 6
- H2 rep 4: commits on main 2
- H3 rep 4: commits on main 2
- H4 rep 4: latency ms {'p50': 258.9, 'max': 374.6}
- H5 rep 4: commits on main 2
- H6 rep 4: controls fired: {'a_stale_review': True, 'b_declared_paths': True, 'c_ci_other_content': True, 'd_self_review': True}
- H1 rep 5: commits on main 6
- H2 rep 5: commits on main 2
- H3 rep 5: commits on main 2
- H4 rep 5: latency ms {'p50': 274.3, 'max': 317.1}
- H5 rep 5: commits on main 2
- H6 rep 5: controls fired: {'a_stale_review': True, 'b_declared_paths': True, 'c_ci_other_content': True, 'd_self_review': True}

## Failed checks

none
