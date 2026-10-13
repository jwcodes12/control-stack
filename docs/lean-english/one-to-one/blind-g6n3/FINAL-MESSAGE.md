All six principal statements are equivalent. All 12 claim/witness gates passed, including clean replay. Full evidence is in [RESULTS.md](/home/opc/projects/blind-work/g6n3/b/docs/lean-english/one-to-one/blind-g6n3/RESULTS.md).

| Claim | Verdict |
|---|---|
| 1 — `progress_interleaved` | EQUIVALENT |
| 2 — `crash_tolerant_progress` | EQUIVALENT |
| 3 — `lossy_safe` | EQUIVALENT |
| 4 — `lossy_rounds` | EQUIVALENT |
| 5 — `lossy_halt_keys` | EQUIVALENT |
| 6 — `tagged_rounds` | EQUIVALENT |

The three most important findings:

1. All back files compiled unchanged; equivalence proofs compare pointwise conclusions without invoking the original target theorems.
2. Claim 6’s auxiliary “strictly weaker” assertion is incorrect as a general predicate implication. A gated counterexample and replacement wording are saved.
3. Claim 1’s execute transition ignores caller identity, so choosing the requester in Back loses no generality.