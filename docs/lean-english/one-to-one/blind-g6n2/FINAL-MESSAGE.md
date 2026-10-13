| Claim | Verdict |
|---|---|
| 1 — `safe_of_sound` | EQUIVALENT |
| 2 — `sc26_safe_disjoint` | EQUIVALENT |
| 3 — `sc26_once` | EQUIVALENT |
| 4 — `halt_freezes` | UNDECIDED |
| 5 — `concrete_safe` | EQUIVALENT |
| 6 — `concrete_halt` | EQUIVALENT |
| 7 — `sc26_safe_authenticated` | EQUIVALENT |
| 8 — `forged_approval_pays_without_auth` | UNDECIDED |
| 9 — `sc26_consent_from_honest_script` | EQUIVALENT |
| 10 — `honest_progress` | EQUIVALENT |

The three most important findings:

1. Claim 4 translates exact list equality into set equality, losing order and multiplicity. Original → Back passed; the same-run converse remains uncertified.
2. Claim 8 replaces singleton-bank equality with membership and strengthens “no exact self-issued approval” to “no approver issued anything.” Both hold on the fixed trace, but that truth was not used to manufacture equivalence.
3. Claims 7 and 9 preserve the crucial distinction: disjointness from `U` alone does not confine adversarial issuers; `AdvTrace` does.

All ten comparison/direction certificates and ten separate witnesses passed. Clean-state `regate.py` exited **0**. Back and typed hashes remain intact.

[RESULTS.md](/home/opc/projects/blind-work/g6n2/b/docs/lean-english/one-to-one/blind-g6n2/RESULTS.md) contains receipts, English corrections, and limitations.