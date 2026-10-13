| Claim | Verdict |
|---|---|
| 1 `runtime_exclusive` | EQUIVALENT |
| 2 `agent_call_legal` | EQUIVALENT |
| 3 `protocol_safe` | EQUIVALENT |
| 4 `one_use` | EQUIVALENT |
| 5 `gate_contract` | EQUIVALENT |
| 6 `broker_contract` | EQUIVALENT |
| 7 `deployment_safe` | EQUIVALENT |
| 8 `accepted_path_safety_monotone` | EQUIVALENT |
| 9 `path_edge_subset` | EQUIVALENT |
| 10 `requested_monotonicity_counterexample` | EQUIVALENT |

Three important findings:

1. All back files compiled unchanged and matched their Phase A hashes. All **20 claim/witness gates passed**, including a clean-state re-gate.
2. Claim 5’s cap caveat is misleading: its invariant includes the spending bound. Replacement wording is recorded.
3. Runtime guarantees remain conditional on extraction and publication premises. SC26 approval does not imply independent artifact review.

[Results, corrections, and receipts](/home/opc/projects/blind-work/g0n1/b/docs/lean-english/one-to-one/blind-g0n1/RESULTS.md) · [Progress](/home/opc/projects/blind-work/g0n1/b/docs/lean-english/one-to-one/blind-g0n1/PROGRESS.md)