| Claim | Verdict |
|---|---|
| 1 — `step_safe` | EQUIVALENT |
| 2 — `trace_safe` | EQUIVALENT |
| 3 — `cap_does_not_prevent` | EQUIVALENT |
| 4 — `zero_dependence_is_blind` | EQUIVALENT |
| 5 — `forbidden_never_executes` | EQUIVALENT |
| 6 — `sc06_safe` | EQUIVALENT |
| 7 — `halt_freezes` | EQUIVALENT |
| 8 — `sc07_safe` | EQUIVALENT |
| 9 — `concrete_safe` | EQUIVALENT |

Three main findings:

1. All nine back files compiled unchanged. All nine comparison gates and nine separate Witness gates passed.
2. Claim 3 required a substantive bridge: the gated proof extracts a deterministic perfect code from arbitrary successful probabilistic rows.
3. Two English passages need correction: claim 4 wrongly excludes uniform-bit coordination; claim 9 should clarify that denied or halted packets do not increase `consumed`.

Receipts, replacement sentences, and the hostile audit are in [RESULTS.md](/home/opc/projects/sol-g1a-b/docs/lean-english/one-to-one/blind-g1a/RESULTS.md). Completion details are in [PROGRESS.md](/home/opc/projects/sol-g1a-b/docs/lean-english/one-to-one/blind-g1a/PROGRESS.md).