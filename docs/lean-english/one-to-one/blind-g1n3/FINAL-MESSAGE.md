| Claim | Verdict |
|---|---|
| 1 — `expected_leak_le` | EQUIVALENT |
| 2 — `observable_schedule_exfil` | EQUIVALENT |
| 3 — `datacenter_example` | EQUIVALENT |
| 4 — `upload_completes` | EQUIVALENT |
| 5 — `exfil_needs_windows` | EQUIVALENT |
| 6 — `shared_quota_blocks` | EQUIVALENT |
| 7 — `concrete_wire_lt` | EQUIVALENT |
| 8 — `concrete_halt_freezes` | EQUIVALENT |
| 9 — `sink_within_quota` | EQUIVALENT |

All **18 comparison and witness gates passed**, including a clean re-gate.

The three most important findings:

1. Claim 2’s capping and claim 3’s fractions, decimals, and conjunction placement preserve meaning; the comparisons were proved pointwise.
2. Claim 5 counts **opened windows**, including empty ones. It establishes no elapsed-time or audit-probability bound.
3. Claim 3’s whole-plan survival caveat and claim 9’s external sink premise need clearer wording. Replacement sentences are recorded.

[Full results and receipts](/home/opc/projects/blind-work/g1n3/b/docs/lean-english/one-to-one/blind-g1n3/RESULTS.md) · [Progress](/home/opc/projects/blind-work/g1n3/b/docs/lean-english/one-to-one/blind-g1n3/PROGRESS.md) · [Re-gate script](/home/opc/projects/blind-work/g1n3/b/docs/lean-english/one-to-one/blind-g1n3/regate.py)