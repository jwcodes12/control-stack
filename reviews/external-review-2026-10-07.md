# External review (2026-10-07, shared by John) and disposition

Verdict: formal foundation strong; empirical pipeline promising, conditional; implementation correspondence a major
gap; deployment assurance not established. Main advice: optimise for uncertainty removed from a realistic safety case,
not the number of verified results.

| point | disposition |
|---|---|
| 1. sampled ROC cannot give the uniform τ in `ComposeGame` | Agreed. Proved as a negative result (`ControlStack/ComposeBlindSpot.lean`: average miss 1/1000, content-adaptive Red risk 1). `ComposeAvg` gives the bound that data CAN support (Red chooses timing, content from the population). The coverage assumption is recorded as UNRESOLVED in every manifest. |
| 2. action layer: build a fail-closed tool gateway | Agreed; P0. Touches the agent runtime, so it needs John's go-ahead. |
| 3. empirical results are not deployment evidence; split mismatch; live sabotage | Agreed. Matched-population check done (`numerics/stat_audit.py`): detection falls from 39/150 to 7/56 at ≥8. Trajectory-max timing is a blocking assumption (`timing_pre_execution`) in every manifest. |
| roadmap reorganisation (P0–P3) | Adopted in ROADMAP §3. UMADAPTF3 (general attainment) shelved as P3. |
| A. machine-readable assumptions | Done: `assurance/*.json`, `tools/assurance.py` (refuses to claim THEOREM_VERIFIED before Lean passes). |
| B. falsifiable implementation tests; environment-state invariants | Planned with the gateway (P0/P2). |
| C. statistical handoff audit | Done for LASR (clean) and LinuxArena (ids stripped: cannot audit repeats; honest completion not reportable from public data). Held-out-for-training vs untouched-for-certification: disclosed per prereg; LASR is the former. |
| D. CI and outside review | CI planned (P1). Human review: John. |
