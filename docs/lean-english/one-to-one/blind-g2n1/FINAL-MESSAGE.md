[RESULTS.md](/home/opc/projects/blind-work/g2n1/b/docs/lean-english/one-to-one/blind-g2n1/RESULTS.md) contains proofs, receipts, and English corrections. All ten back files compiled unchanged. Clean-state regating passed all ten claims and ten witnesses.

| Claim | Verdict |
|---|---|
| 1 — SC08.sc08_safe | EQUIVALENT |
| 2 — SC08.safe_of_sound | ENGLISH_STRONGER |
| 3 — SC08.halt_freezes | EQUIVALENT |
| 4 — SC09.sc09_safe | EQUIVALENT |
| 5 — SC09.spawn_attenuates | EQUIVALENT |
| 6 — SC09.halt_freezes | EQUIVALENT |
| 7 — SC10.sc10_safe | EQUIVALENT |
| 8 — SC10.policy_admin_only | EQUIVALENT |
| 9 — SC10.halt_freezes | EQUIVALENT |
| 10 — SC12.sc12_safe | EQUIVALENT |

The three most important findings:

1. **Claim 2 broadens initial-state scope:** Back allows either halted flag; Orig fixes `false`. The stronger verdict concerns parameter coverage, with identical conclusions on the original domain.
2. **Claim 5’s “sub-collection” means membership inclusion**, without comparing counts or order.
3. **Two prose details need correction:** an unrecognised interpreter’s script argument is unchecked but unrecorded; SC12 bypass operations have no claimed session label.