All 10 pointwise comparisons and all 10 separately gated witnesses passed. [RESULTS.md](/home/opc/projects/blind-work/g7n1/b/docs/lean-english/one-to-one/blind-g7n1/RESULTS.md) contains receipts, corrections and supporting evidence.

| Claim | Verdict |
|---|---|
| 1 — `rollback_transfer` | EQUIVALENT |
| 2 — `sc27_safe` | EQUIVALENT |
| 3 — `tamper_after_anchor_detected` | EQUIVALENT |
| 4 — `halt_freezes` | EQUIVALENT |
| 5 — `sc27_ext_safe` | EQUIVALENT |
| 6 — `tampered_never_anchored` | EQUIVALENT |
| 7 — `anchors_chain` | EQUIVALENT |
| 8 — `alarm_iff` | EQUIVALENT |
| 9 — `concrete_ext_safe` | EQUIVALENT |
| 10 — `concrete_tampered_never_anchored` | EQUIVALENT |

The three most important findings:

- Claims **5, 9 and 10 omit initialization**. Equivalence uses Phase A’s documented empty-state interpretation.
- Claim **1’s rollback-then-write halt aside is too broad**. Restoring the current committed record can permit further commits; a gated witness demonstrates this.
- Claim **2 overstates hash unprovability**. Injectivity on a specified finite set can be proved even for a compressing hash.

`regate.py` passed from scratch, exited zero, and changed only receipts and receipt logs.