| Claim | Verdict |
|---|---|
| 1 `sc21_safe` | EQUIVALENT |
| 2 `sc21_undetected_prob` | EQUIVALENT |
| 3 `sc21_undetected_le_pow` | EQUIVALENT |
| 4 `observable_sample_nogo` | EQUIVALENT |
| 5 `sc21_adaptive` | EQUIVALENT |
| 6 `sc21_adaptive_content` | EQUIVALENT |
| 7 `sc21_adaptive_recall` | ENGLISH_WEAKER |
| 8 `sc22_unreplicated_misreport` | EQUIVALENT |
| 9 `sc23_safe` | EQUIVALENT |
| 10 `halt_freezes` | EQUIVALENT |

All ten back files compiled unchanged. All ten claim gates and ten separate witness gates passed, including clean-state re-gating.

The three main findings:

1. **Claim 7 narrows coverage:** Back adds a full-choice marginal premise absent from Orig. A gated certificate proves it is nonredundant; conclusions agree on the common domain.
2. **Claims 2 and 8 need `B ≤ N` for probability language:** otherwise the sample family is empty, although Lean’s totalized ratio remains defined.
3. **Claims 6 and 7 cover finite hidden types:** “arbitrary hidden component” needs that qualification.

Receipts, English corrections, and the complete audit are in [RESULTS.md](/home/opc/projects/blind-work/g5n1/b/docs/lean-english/one-to-one/blind-g5n1/RESULTS.md). Reproduce with [regate.py](/home/opc/projects/blind-work/g5n1/b/docs/lean-english/one-to-one/blind-g5n1/regate.py).