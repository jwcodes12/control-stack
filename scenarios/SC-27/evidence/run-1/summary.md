# SC-27 anchored evidence chain (evidence, PREREG-SC27-ANCHOR-v1)

- commit: `d5427dba83c85cb29b256cd7caa5f547458dafe5` (harness/prereg status: `clean`)
- calibration: FIXED, TAU_A = 0.05 s, TAU_W = 0.05 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T07:06:54.668163Z, finished 2026-10-09T07:07:29.341967Z, wall 34.7 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 1: max time to acceptance 0.2605620239628479 s
- H3 rep 1: max window 0.238364799 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 1: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H1 rep 2: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 2: max time to acceptance 0.24576232698746026 s
- H3 rep 2: max window 0.234774314 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 2: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H1 rep 3: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 3: max time to acceptance 0.25718670000787824 s
- H3 rep 3: max window 0.240644921 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, False, True), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 3: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H1 rep 4: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 4: max time to acceptance 0.2440488450229168 s
- H3 rep 4: max window 0.241533002 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, True, False), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 4: controls fired: {'a_current_head': True, 'b_writer_heads': True}
- H1 rep 5: tamper results {'modify an old entry': {'accepted': False, 'witness': 'fork'}, 'reorder two entries': {'accepted': False, 'witness': 'fork'}, 'truncate the last 3': {'accepted': False, 'witness': 'fork'}, 'append an unanchored suffix': {'accepted': False, 'witness': None}, 'full rewrite with recomputed hashes': {'accepted': False, 'witness': 'fork'}}
- H2 rep 5: max time to acceptance 0.23545559495687485 s
- H3 rep 5: max window 0.234395193 s; (delay, anchored before rewrite, rewrite accepted): [(0.0, False, True), (0.0417, False, True), (0.0833, False, True), (0.125, False, True), (0.1667, False, True), (0.2083, True, False), (0.25, True, False), (0.2917, True, False), (0.3333, True, False), (0.375, True, False)]
- H4 rep 5: controls fired: {'a_current_head': True, 'b_writer_heads': True}

## Failed checks

none
