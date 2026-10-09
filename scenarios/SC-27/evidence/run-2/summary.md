# SC-27 anchored evidence chain v2 (evidence, PREREG-SC27-ANCHOR-v2)

- commit: `feff38b953e7879e17dbeb67874254ef8af193ff` (harness/prereg status: `clean`)
- calibration: FIXED, TAU_A = 0.05 s, TAU_W = 0.05 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:57:02.268980Z, finished 2026-10-09T15:57:36.734218Z, wall 34.5 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | NEGATIVE_CONTROL | 5/5 | PASS |
| H5 | claim | 5/5 | PASS |
| H6 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 1: max time to acceptance 0.24517396895680577 s
- H3 rep 1: max window 0.238408281 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 1: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H5 rep 1: v2 witness after truncation to empty: {'empty file': {'after': 'fork', 'empty_accepted': False}, 'deleted file': {'after': 'fork', 'empty_accepted': False}}
- H6 rep 1: v1 witness after truncation to empty: {'empty file': 'empty', 'deleted file': 'empty'}, fork records 0
- H1 rep 2: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 2: max time to acceptance 0.2479328520130366 s
- H3 rep 2: max window 0.237811761 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 2: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H5 rep 2: v2 witness after truncation to empty: {'empty file': {'after': 'fork', 'empty_accepted': False}, 'deleted file': {'after': 'fork', 'empty_accepted': False}}
- H6 rep 2: v1 witness after truncation to empty: {'empty file': 'empty', 'deleted file': 'empty'}, fork records 0
- H1 rep 3: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 3: max time to acceptance 0.24507892900146544 s
- H3 rep 3: max window 0.242716767 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 3: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H5 rep 3: v2 witness after truncation to empty: {'empty file': {'after': 'fork', 'empty_accepted': False}, 'deleted file': {'after': 'fork', 'empty_accepted': False}}
- H6 rep 3: v1 witness after truncation to empty: {'empty file': 'empty', 'deleted file': 'empty'}, fork records 0
- H1 rep 4: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 4: max time to acceptance 0.24465672892984003 s
- H3 rep 4: max window 0.236562159 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 4: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H5 rep 4: v2 witness after truncation to empty: {'empty file': {'after': 'fork', 'empty_accepted': False}, 'deleted file': {'after': 'fork', 'empty_accepted': False}}
- H6 rep 4: v1 witness after truncation to empty: {'empty file': 'empty', 'deleted file': 'empty'}, fork records 0
- H1 rep 5: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 5: max time to acceptance 0.24280196707695723 s
- H3 rep 5: max window 0.22896171 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, True, False), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 5: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H5 rep 5: v2 witness after truncation to empty: {'empty file': {'after': 'fork', 'empty_accepted': False}, 'deleted file': {'after': 'fork', 'empty_accepted': False}}
- H6 rep 5: v1 witness after truncation to empty: {'empty file': 'empty', 'deleted file': 'empty'}, fork records 0

## Failed checks

none
