Completed. All eight comparison gates and eight witness gates passed.

| Claim | Verdict |
|---|---|
| 1 — Accepted | **ENGLISH_STRONGER** |
| 2 — exclusive_sink | EQUIVALENT |
| 3 — database_custody | EQUIVALENT |
| 5 — agent_not_receiver_uid | EQUIVALENT |
| 12 — accepted_no_avoided_path | EQUIVALENT |
| 16 — deployment_broker_safe | EQUIVALENT |
| 20 — halted_absorbing | EQUIVALENT |
| 23 — runtime_trace | EQUIVALENT |

The three main findings:

1. Claim 1’s frozen blind reading compares unequal node **records**; Lean compares unequal **IDs**. A gated reviewer/approver collision proves the blind predicate strictly stronger.
2. The other seven conclusions match pointwise under the same hypotheses. Their equivalence proofs do not rely on both closed theorems being true.
3. “Mediated edges are not examined further” is too broad: they stop reachability traversal but still undergo basic and applicable writer checks.

[RESULTS.md](/home/opc/projects/sol-g0-stale/docs/lean-english/one-to-one/blind-v1/RESULTS.md) contains receipts, corrections, and the over-reading audit. [PROGRESS.md](/home/opc/projects/sol-g0-stale/docs/lean-english/one-to-one/blind-v1/PROGRESS.md) records timing and retained failures.