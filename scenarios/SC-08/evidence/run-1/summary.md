# SC-08 application allowlisting (evidence, PREREG-SC08-EXEC-v1)

- commit: `f4ab5d23c0b7bb62a3c0e72d82f31d2e221a55ca` (harness/prereg status: `clean`)
- calibration: FIXED, L_RUN = 1.05 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T15:02:25.385679Z, finished 2026-10-09T15:02:53.663161Z, wall 28.3 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | claim | 5/5 | PASS |
| H5 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: decisions {'hello_a': ('executed', None), 'hello_b': ('executed', None), 'hello_c': ('executed', None), 'staging copy of allowlisted content': ('executed', None), 'staging non-allowlisted script': ('refused', 'script digest not allowlisted'), 'non-allowlisted program (/bin/sh)': ('refused', 'program digest not allowlisted')}
- H2 rep 1: valid swaps [True, True, True], ran ['ceb0d9b15e8f', 'ceb0d9b15e8f', 'ceb0d9b15e8f']
- H3 rep 1: decisions ['script digest not allowlisted', 'interpreter without a script (REPL) refused']
- H4 rep 1: latency ms {'p50': 152.43, 'max': 301.31}
- H5 rep 1: a ran ['90aa56395d5c', '90aa56395d5c']; b executed executed/executed
- H1 rep 2: decisions {'hello_a': ('executed', None), 'hello_b': ('executed', None), 'hello_c': ('executed', None), 'staging copy of allowlisted content': ('executed', None), 'staging non-allowlisted script': ('refused', 'script digest not allowlisted'), 'non-allowlisted program (/bin/sh)': ('refused', 'program digest not allowlisted')}
- H2 rep 2: valid swaps [True, True, True], ran ['ceb0d9b15e8f', 'ceb0d9b15e8f', 'ceb0d9b15e8f']
- H3 rep 2: decisions ['script digest not allowlisted', 'interpreter without a script (REPL) refused']
- H4 rep 2: latency ms {'p50': 48.78, 'max': 134.6}
- H5 rep 2: a ran ['90aa56395d5c', '90aa56395d5c']; b executed executed/executed
- H1 rep 3: decisions {'hello_a': ('executed', None), 'hello_b': ('executed', None), 'hello_c': ('executed', None), 'staging copy of allowlisted content': ('executed', None), 'staging non-allowlisted script': ('refused', 'script digest not allowlisted'), 'non-allowlisted program (/bin/sh)': ('refused', 'program digest not allowlisted')}
- H2 rep 3: valid swaps [True, True, True], ran ['ceb0d9b15e8f', 'ceb0d9b15e8f', 'ceb0d9b15e8f']
- H3 rep 3: decisions ['script digest not allowlisted', 'interpreter without a script (REPL) refused']
- H4 rep 3: latency ms {'p50': 39.98, 'max': 76.97}
- H5 rep 3: a ran ['90aa56395d5c', '90aa56395d5c']; b executed executed/executed
- H1 rep 4: decisions {'hello_a': ('executed', None), 'hello_b': ('executed', None), 'hello_c': ('executed', None), 'staging copy of allowlisted content': ('executed', None), 'staging non-allowlisted script': ('refused', 'script digest not allowlisted'), 'non-allowlisted program (/bin/sh)': ('refused', 'program digest not allowlisted')}
- H2 rep 4: valid swaps [True, True, True], ran ['ceb0d9b15e8f', 'ceb0d9b15e8f', 'ceb0d9b15e8f']
- H3 rep 4: decisions ['script digest not allowlisted', 'interpreter without a script (REPL) refused']
- H4 rep 4: latency ms {'p50': 117.38, 'max': 210.48}
- H5 rep 4: a ran ['90aa56395d5c', '90aa56395d5c']; b executed executed/executed
- H1 rep 5: decisions {'hello_a': ('executed', None), 'hello_b': ('executed', None), 'hello_c': ('executed', None), 'staging copy of allowlisted content': ('executed', None), 'staging non-allowlisted script': ('refused', 'script digest not allowlisted'), 'non-allowlisted program (/bin/sh)': ('refused', 'program digest not allowlisted')}
- H2 rep 5: valid swaps [True, True, True], ran ['ceb0d9b15e8f', 'ceb0d9b15e8f', 'ceb0d9b15e8f']
- H3 rep 5: decisions ['script digest not allowlisted', 'interpreter without a script (REPL) refused']
- H4 rep 5: latency ms {'p50': 38.03, 'max': 121.72}
- H5 rep 5: a ran ['90aa56395d5c', '90aa56395d5c']; b executed executed/executed

## Failed checks

none
