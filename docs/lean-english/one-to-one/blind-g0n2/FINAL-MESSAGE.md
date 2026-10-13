| Claim | Verdict | Claim / Witness gates |
|---|---|---|
| 1 `indexed_receipts_sound` | EQUIVALENT | PASS / PASS |
| 2 `transaction_preserves` | EQUIVALENT | PASS / PASS |
| 3 `transaction_coherent` | EQUIVALENT | PASS / PASS |
| 4 `committed_nonce_unusable` | EQUIVALENT | PASS / PASS |
| 5 `trace_preserves` | EQUIVALENT | PASS / PASS |
| 6 `final_safe` | EQUIVALENT | PASS / PASS |
| 7 `replay_was_not_allowed` | EQUIVALENT | PASS / PASS |
| 8 `omitted_tail_is_accepted` | EQUIVALENT | PASS / PASS |

Three main findings:

1. All eight back translations compiled unchanged and were hashed before originals were opened. Pointwise equivalence and concrete witnesses passed all **16 gates**, including clean-state regating.
2. “A shorter list also passes” needs qualification: the nine-receipt prefix passes; the tested middle deletions fail.
3. A different nonce still requires the **entire `Allowed` guard**, not merely lease and global budgets.

Receipts, per-claim audits, replacement English, and reproduction instructions are in [RESULTS.md](/home/opc/projects/blind-work/g0n2/b/docs/lean-english/one-to-one/blind-g0n2/RESULTS.md).