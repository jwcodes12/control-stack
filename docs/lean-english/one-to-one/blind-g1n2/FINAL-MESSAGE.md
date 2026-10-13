All 20 deterministic gates passed, including separate witnesses. All back files compiled unchanged. Clean `regate.py` exited 0.

| Claim | Verdict |
|---|---|
| 1 `sc01_case` | EQUIVALENT |
| 2 `core_bound` | EQUIVALENT |
| 3 `covert_bound_lifetime` | EQUIVALENT |
| 4 `sc02_accumulated` | EQUIVALENT |
| 5 `rekey_epoch` | EQUIVALENT |
| 6 `log_channel` | EQUIVALENT |
| 7 `canonical_seq` | EQUIVALENT |
| 8 `windows_needed` | EQUIVALENT |
| 9 `sc07_mixed` | EQUIVALENT |
| 10 `sc07_fixed_budget` | ENGLISH_STRONGER |

Three important findings:

1. Claim 10 permits traffic-certificate mass **≤ 1**; the original requires **= 1**. The gate certifies specialization and a strictly larger hypothesis domain.
2. Claims 4–5 need normalization to justify calling the weighted expression a probability. A gated claim 4 example has success value **2**.
3. Claim 2’s blanking description needs **“before the first close.”** Later events preserve the frozen snapshot.

Receipts, corrections, and ambiguity reviews are in [RESULTS.md](/home/opc/projects/blind-work/g1n2/b/docs/lean-english/one-to-one/blind-g1n2/RESULTS.md). Completion details are in [PROGRESS.md](/home/opc/projects/blind-work/g1n2/b/docs/lean-english/one-to-one/blind-g1n2/PROGRESS.md).