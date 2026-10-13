| Claim | Verdict |
|---|---|
| 1 — sc18_safe | EQUIVALENT |
| 2 — config_untampered | EQUIVALENT |
| 3 — halt_freezes | EQUIVALENT |
| 4 — sc18_safe_authenticated | EQUIVALENT |
| 5 — forged18_redirects_without_auth | EQUIVALENT |
| 6 — honest_release | EQUIVALENT |
| 7 — progress_interleaved | EQUIVALENT |
| 8 — silent_ticks_halt | EQUIVALENT |
| 9 — resume_safe | EQUIVALENT |
| 10 — resume_progress | EQUIVALENT |

All **formal comparisons** and separate witnesses passed: 20/20 gates. Clean re-gating exited 0 and preserved every saved Lean input.

The three most important findings:

1. **Claim 3’s clock aside is false.** Halted ticks leave the state unchanged; the clock freezes.
2. **Sink outage does not immediately prevent releases.** An acknowledged request can still be released before watchdog halt.
3. **Claims 6 and 10 assert final membership.** They need not produce a fresh release or repair an earlier unsafe record.

Receipts, corrections and ambiguity analysis are in [RESULTS.md](/home/opc/projects/blind-work/g4n1/b/docs/lean-english/one-to-one/blind-g4n1/RESULTS.md). Completion details are in [PROGRESS.md](/home/opc/projects/blind-work/g4n1/b/docs/lean-english/one-to-one/blind-g4n1/PROGRESS.md); reproduction uses [regate.py](/home/opc/projects/blind-work/g4n1/b/docs/lean-english/one-to-one/blind-g4n1/regate.py).