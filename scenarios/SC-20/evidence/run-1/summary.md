# SC-20 data provenance (evidence, PREREG-SC20-PROV-v1)

- commit: `9cc79d7605eaa6836e0e6fa61a7eecda91b5a74e` (harness/prereg status: `clean`)
- calibration: FIXED, L_TRAIN = 0.25 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T07:26:47.117928Z, finished 2026-10-09T07:27:03.727022Z, wall 16.6 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | claim | 5/5 | PASS |
| H5 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: consumed 13
- H2 rep 1: consumed 8
- H3 rep 1: consumed 5
- H4 rep 1: freeze + train 0.0334 s, stat {'n': 220, 'hash': 'f658569636126e5d5e22faef238975980e1bc9c11235b36a55d87ce7d0f0a67a', 'label_mean': 0.481818}
- H5 rep 1: controls fired: {'a_no_quarantine': True, 'b_no_recheck': True, 'c_unlisted_source': True}
- H1 rep 2: consumed 13
- H2 rep 2: consumed 8
- H3 rep 2: consumed 5
- H4 rep 2: freeze + train 0.0337 s, stat {'n': 220, 'hash': 'f658569636126e5d5e22faef238975980e1bc9c11235b36a55d87ce7d0f0a67a', 'label_mean': 0.481818}
- H5 rep 2: controls fired: {'a_no_quarantine': True, 'b_no_recheck': True, 'c_unlisted_source': True}
- H1 rep 3: consumed 13
- H2 rep 3: consumed 8
- H3 rep 3: consumed 5
- H4 rep 3: freeze + train 0.0309 s, stat {'n': 220, 'hash': 'f658569636126e5d5e22faef238975980e1bc9c11235b36a55d87ce7d0f0a67a', 'label_mean': 0.481818}
- H5 rep 3: controls fired: {'a_no_quarantine': True, 'b_no_recheck': True, 'c_unlisted_source': True}
- H1 rep 4: consumed 13
- H2 rep 4: consumed 8
- H3 rep 4: consumed 5
- H4 rep 4: freeze + train 0.0322 s, stat {'n': 220, 'hash': 'f658569636126e5d5e22faef238975980e1bc9c11235b36a55d87ce7d0f0a67a', 'label_mean': 0.481818}
- H5 rep 4: controls fired: {'a_no_quarantine': True, 'b_no_recheck': True, 'c_unlisted_source': True}
- H1 rep 5: consumed 13
- H2 rep 5: consumed 8
- H3 rep 5: consumed 5
- H4 rep 5: freeze + train 0.032 s, stat {'n': 220, 'hash': 'f658569636126e5d5e22faef238975980e1bc9c11235b36a55d87ce7d0f0a67a', 'label_mean': 0.481818}
- H5 rep 5: controls fired: {'a_no_quarantine': True, 'b_no_recheck': True, 'c_unlisted_source': True}

## Failed checks

none
