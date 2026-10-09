# SC-10/11 policy store and pinned toolchain (evidence, PREREG-SC10-POLICY-v1)

- commit: `fabf2ad36d29a7a3fddbec3d43b01867a0e7c3ae` (harness/prereg status: `clean`)
- calibration: FIXED, L_DEC = 0.1 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:27:46.285100Z, finished 2026-10-09T15:28:18.098328Z, wall 31.8 s
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

- H1 rep 1: decisions 40, versions used [0, 1, 2], stale 0
- H2 rep 1: decisions 6, versions used [0], stale 0
- H3 rep 1: decisions 42, versions used [0, 1], stale 0
- H4 rep 1: toolchains that ran ['pinned']; misinstalled toolchain digest mismatch
- H5 rep 1: latency ms {'p50': 4.42, 'max': 20.0}
- H6 rep 1: controls fired: {'a_agent_writable_policy': True, 'b_cached_policy': True, 'c_alternate_evaluator': True, 'd_path_toolchain': True}; cached-policy stale window 0.4613 s
- H1 rep 2: decisions 40, versions used [0, 1, 2], stale 0
- H2 rep 2: decisions 6, versions used [0], stale 0
- H3 rep 2: decisions 42, versions used [0, 1], stale 0
- H4 rep 2: toolchains that ran ['pinned']; misinstalled toolchain digest mismatch
- H5 rep 2: latency ms {'p50': 3.92, 'max': 23.75}
- H6 rep 2: controls fired: {'a_agent_writable_policy': True, 'b_cached_policy': True, 'c_alternate_evaluator': True, 'd_path_toolchain': True}; cached-policy stale window 0.4875 s
- H1 rep 3: decisions 40, versions used [0, 1, 2], stale 0
- H2 rep 3: decisions 6, versions used [0], stale 0
- H3 rep 3: decisions 42, versions used [0, 1], stale 0
- H4 rep 3: toolchains that ran ['pinned']; misinstalled toolchain digest mismatch
- H5 rep 3: latency ms {'p50': 0.75, 'max': 7.42}
- H6 rep 3: controls fired: {'a_agent_writable_policy': True, 'b_cached_policy': True, 'c_alternate_evaluator': True, 'd_path_toolchain': True}; cached-policy stale window 0.4954 s
- H1 rep 4: decisions 40, versions used [0, 1, 2], stale 0
- H2 rep 4: decisions 6, versions used [0], stale 0
- H3 rep 4: decisions 42, versions used [0, 1], stale 0
- H4 rep 4: toolchains that ran ['pinned']; misinstalled toolchain digest mismatch
- H5 rep 4: latency ms {'p50': 1.35, 'max': 9.9}
- H6 rep 4: controls fired: {'a_agent_writable_policy': True, 'b_cached_policy': True, 'c_alternate_evaluator': True, 'd_path_toolchain': True}; cached-policy stale window 0.488 s
- H1 rep 5: decisions 40, versions used [0, 1, 2], stale 0
- H2 rep 5: decisions 6, versions used [0], stale 0
- H3 rep 5: decisions 42, versions used [0, 1], stale 0
- H4 rep 5: toolchains that ran ['pinned']; misinstalled toolchain digest mismatch
- H5 rep 5: latency ms {'p50': 4.94, 'max': 17.32}
- H6 rep 5: controls fired: {'a_agent_writable_policy': True, 'b_cached_policy': True, 'c_alternate_evaluator': True, 'd_path_toolchain': True}; cached-policy stale window 0.4837 s

## Failed checks

none
