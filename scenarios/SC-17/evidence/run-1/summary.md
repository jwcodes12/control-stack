# SC-17 drift reconcile (evidence, PREREG-SC17-DRIFT-v1)

- commit: `6ee5e21b3922605cac8a14c02b51424713df8567` (harness/prereg status: `clean`)
- calibration: FIXED, TAU_N = 3, TAU_L = 0.05 s, L_APPLY = 0.15 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T06:50:27.475963Z, finished 2026-10-09T06:51:02.054635Z, wall 34.6 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | claim | 5/5 | PASS |
| H5 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: max oob live 10 (sampled 9), max lifetime 0.201 s, reconciler max late 0.002855 s
- H2 rep 1: applies 2
- H3 rep 1: applies 1
- H4 rep 1: latency ms {'p50': 7.85, 'max': 10.08}
- H5 rep 1: a: {'series': [20, 40, 60, 80], 'alive': 80, 'max_age_alive_s': 1.95, 'died': 0}; b: B applied True
- H1 rep 2: max oob live 10 (sampled 10), max lifetime 0.201 s, reconciler max late 0.000324 s
- H2 rep 2: applies 2
- H3 rep 2: applies 1
- H4 rep 2: latency ms {'p50': 7.78, 'max': 10.75}
- H5 rep 2: a: {'series': [20, 40, 60, 80], 'alive': 80, 'max_age_alive_s': 1.951, 'died': 0}; b: B applied True
- H1 rep 3: max oob live 10 (sampled 10), max lifetime 0.201 s, reconciler max late 0.001213 s
- H2 rep 3: applies 2
- H3 rep 3: applies 1
- H4 rep 3: latency ms {'p50': 8.63, 'max': 18.56}
- H5 rep 3: a: {'series': [20, 40, 60, 80], 'alive': 80, 'max_age_alive_s': 1.95, 'died': 0}; b: B applied True
- H1 rep 4: max oob live 10 (sampled 8), max lifetime 0.201 s, reconciler max late 0.000725 s
- H2 rep 4: applies 2
- H3 rep 4: applies 1
- H4 rep 4: latency ms {'p50': 8.44, 'max': 14.42}
- H5 rep 4: a: {'series': [20, 40, 60, 80], 'alive': 80, 'max_age_alive_s': 1.95, 'died': 0}; b: B applied True
- H1 rep 5: max oob live 10 (sampled 8), max lifetime 0.201 s, reconciler max late 0.000278 s
- H2 rep 5: applies 2
- H3 rep 5: applies 1
- H4 rep 5: latency ms {'p50': 8.24, 'max': 10.49}
- H5 rep 5: a: {'series': [20, 40, 60, 80], 'alive': 80, 'max_age_alive_s': 1.95, 'died': 0}; b: B applied True

## Failed checks

none
