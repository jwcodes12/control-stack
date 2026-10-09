# SC-04 log canonicaliser (evidence, PREREG-SC04-LOGCANON-v1)

- commit: `2ba7e3133b5251ae136e9f1335c97028a63b5a3b` (harness/prereg status: `clean`)
- calibration: FIXED, N_TOKENS = 4000, alphabet K*Q^f = 128
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:48:30.968197Z, finished 2026-10-09T15:48:54.536253Z, wall 23.6 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: schema records 40, defects 0
- H2 rep 1: m=1: acc 0.0320 <= bound 0.032 (distinct views 128/128); m=2: acc 0.8960 <= bound 1 (distinct views 3584/128)
- H3 rep 1: per-template counts match: True
- H4 rep 1: token recovered True
- H1 rep 2: schema records 40, defects 0
- H2 rep 2: m=1: acc 0.0320 <= bound 0.032 (distinct views 128/128); m=2: acc 0.8870 <= bound 1 (distinct views 3548/128)
- H3 rep 2: per-template counts match: True
- H4 rep 2: token recovered True
- H1 rep 3: schema records 40, defects 0
- H2 rep 3: m=1: acc 0.0320 <= bound 0.032 (distinct views 128/128); m=2: acc 0.8878 <= bound 1 (distinct views 3551/128)
- H3 rep 3: per-template counts match: True
- H4 rep 3: token recovered True
- H1 rep 4: schema records 40, defects 0
- H2 rep 4: m=1: acc 0.0320 <= bound 0.032 (distinct views 128/128); m=2: acc 0.8948 <= bound 1 (distinct views 3579/128)
- H3 rep 4: per-template counts match: True
- H4 rep 4: token recovered True
- H1 rep 5: schema records 40, defects 0
- H2 rep 5: m=1: acc 0.0320 <= bound 0.032 (distinct views 128/128); m=2: acc 0.8880 <= bound 1 (distinct views 3552/128)
- H3 rep 5: per-template counts match: True
- H4 rep 5: token recovered True

## Failed checks

none
