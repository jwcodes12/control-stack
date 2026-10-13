All 20 Claim and Witness gates passed. Clean-state `regate.py` exited 0.

| Claim | Verdict |
|---|---|
| 1 — concrete_safe | EQUIVALENT |
| 2 — concrete_durable | EQUIVALENT |
| 3 — sc19_safe | EQUIVALENT |
| 4 — SC19.halt_freezes | EQUIVALENT |
| 5 — sc19_safe_authenticated | EQUIVALENT |
| 6 — forged19_destroys_without_auth | EQUIVALENT |
| 7 — sc20_safe | EQUIVALENT |
| 8 — SC20.halt_freezes | EQUIVALENT |
| 9 — sc20_safe_authenticated | EQUIVALENT |
| 10 — forged20_trains_without_auth | EQUIVALENT |

The three main findings:

1. Claim 1 omits an acknowledgement-count bound. Independent induction recovers it for reachable states; equivalence fails on arbitrary fabricated states.
2. Claims 5 and 9 use predicate sets where the originals use lists. Gated finite-trace adapters resolve that difference.
3. SC20 remains a digest-level guarantee. It adds no cleanliness, allowlist, reviewer/writer distinction, or frozen-content equality to the conclusion; the English caveats are respected.

[Results, receipts and proposed English corrections](/home/opc/projects/blind-work/g4n2/b/docs/lean-english/one-to-one/blind-g4n2/RESULTS.md) · [Progress](/home/opc/projects/blind-work/g4n2/b/docs/lean-english/one-to-one/blind-g4n2/PROGRESS.md)