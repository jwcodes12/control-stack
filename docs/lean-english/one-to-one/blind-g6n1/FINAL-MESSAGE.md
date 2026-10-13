[RESULTS.md](/home/opc/projects/blind-work/g6n1/b/docs/lean-english/one-to-one/blind-g6n1/RESULTS.md) contains receipts, proofs, and English corrections. All **20 claim/Witness gates passed**; clean re-gating exited 0.

| Claim | Verdict |
|---|---|
| 1 — sc25_safe | EQUIVALENT |
| 2 — expired_never_executes | EQUIVALENT |
| 3 — halt_freezes | EQUIVALENT |
| 4 — sc25_content_safe | EQUIVALENT |
| 5 — digest_only_executes_unaudited | EQUIVALENT |
| 6 — sc25_safe_authenticated | EQUIVALENT |
| 7 — forged25_executes_without_auth | EQUIVALENT |
| 8 — concrete_safe | EQUIVALENT |
| 9 — concrete_content_safe | EQUIVALENT |
| 10 — sc26_safe | EQUIVALENT |

Three important findings:

- All back files compiled unchanged. Phase-A hashes matched, and typed hashes were frozen before originals were opened.
- Claim 6 needed a causal trace-origin bridge; claims 5 and 7 needed singleton-log bridges. Equivalence was not manufactured from two closed true theorems.
- The prose needs qualifications: claims 2 and 3 assume arbitrary states without certified expiry/halt histories; claim 10 should distinguish modeled bank facts from real-bank guarantees.