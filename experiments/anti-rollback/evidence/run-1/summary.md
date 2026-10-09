# Anti-rollback run (evidence, PREREG-ANTI-ROLLBACK-v1)

- commit: `2ee51d0913f1a8711657ea1363a42dc38bf5d047` (harness/prereg status: `clean`)
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`, sqlite `3.34.1`
- started 2026-10-09T14:20:27.150320Z, finished 2026-10-09T14:20:48.053292Z, wall 20.9 s
- overall: **PASS**

| hypothesis | cases passed | verdict |
|---|---|---|
| H1 | 35/35 | PASS |
| H2 | 25/25 | PASS |
| H3 | 5/5 | PASS |
| H4 (negative control) | 5/5 | PASS |

H2 restart -> READY: max 0.067 s, median 0.046 s (bound 1.00 s)

## Failed checks

none
