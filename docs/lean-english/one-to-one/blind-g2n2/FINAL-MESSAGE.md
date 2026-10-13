| Claim | Verdict |
|---|---|
| 1 — no_fire_after_end | EQUIVALENT |
| 2 — SC12.halt_freezes | EQUIVALENT |
| 3 — sc12_safe_authenticated | EQUIVALENT |
| 4 — forged12_spawns_without_auth | ENGLISH_STRONGER |
| 5 — trace_safe | EQUIVALENT |
| 6 — app_cannot_effect | EQUIVALENT |
| 7 — sc14_safe | EQUIVALENT |
| 8 — SC14.halt_freezes | EQUIVALENT |

All back files compiled unchanged. All 16 claim/witness gate checks passed, including a clean-state regate.

The three main findings:

1. **Claim 4 strengthens the output predicate:** whole-state equality to `init` versus an empty live list. The concrete trace satisfies both; the strictness counterexample concerns arbitrary output states.
2. **Claim 3 should explicitly name `SC12.init`.** Its provenance conclusion otherwise matches the original after rearranging existential witnesses.
3. **Claim 5 overcredits `dispatch_audit_first`.** That lemma gives list-append equalities, not temporal ordering of database writes.

[Full results, receipts, corrections and reproduction details](/home/opc/projects/blind-work/g2n2/b/docs/lean-english/one-to-one/blind-g2n2/RESULTS.md).