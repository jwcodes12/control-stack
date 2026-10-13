# Phase B progress

**Done:** all ten claims. Verdicts: 8 EQUIVALENT, 2 ENGLISH_WEAKER (4 and 9). No unfinished, UNDECIDED or NOT_FORMALISABLE claims.

- Verified all ten Phase A back-file hashes against `back/BACK-HASHES.json`.
- Compiled every original back file, without changing it; all ten passed.
- Saved byte-identical typed copies and their hashes before opening originals. No typing/syntax repairs were needed; each `compile-fixes/<n>.diff` records no repair and no meaning change.
- Read the named original declarations and required predicate/transition definitions.
- Saved ten `PL_bg3n1_<n>.Claim`/`Witness` statement files and ten proof files, with each original theorem independently type-checked against `OrigClosed`.
- Proved eight pointwise equivalences, including hypothesis iff proofs for 3, 6, 8 and 10.
- Proved `Orig → Back` and counterexamples to `Back → Orig` for the log conclusions of 4 and 9, without manufacturing equivalence from two closed true propositions.
- Deterministically gated all ten Claims and separately all ten Witnesses. All twenty final checks passed; only permitted axioms `propext` and `Quot.sound` appeared.
- Preserved failed comparison-harness development attempts under `attempts/1/` and `attempts/2/`; these did not change the frozen back files. Preserved initial successful receipts under `attempts/3/`.
- Ran `regate.py` from a state with no live receipts and no gate scratch directory. It regenerated all twenty receipts, passed every gate, and exited 0. Frozen persistent inputs remained unchanged and no scratch Lean files remained.
- Audited receipt hashes against all saved statements/proofs and verified the copied gate helper is byte-identical to the supplied helper.
- Wrote `RESULTS.md`, including corrections, ambiguity analysis and each Does NOT say boundary.

**Not done:** nothing required by the requested ten-claim Phase B run.

**Time:** started approximately 2026-10-13 04:12 UTC; typed hashes frozen at 04:13:22.934941 UTC; clean re-gate and final hash audit finished by 04:25:02 UTC (approximately 13 minutes).

**What could not be established:** the Lean conclusions do not certify actual platform identity, accurate real-world paths, competent review, harmless content, or absence of gate bypasses. Those remain the English's declared world premises. For 4 and 9, the strictness counterexamples concern the information expressed by their observed-log predicates, not different executions of the named fixed trace; both named executions were separately checked as Witnesses.

All authored files are under this directory. No git commands, downloads or `ControlStack/` edits were made. No other English/comparison material was consulted beyond the permitted input/back/gate material and the explicitly identified claim list.

Recheck from the repository root:

```bash
python3 docs/lean-english/one-to-one/blind-g3n1/regate.py
```

Receipts: `bg3n1_<n>.receipt.json` and `bg3n1_<n>.witness.receipt.json`. Clean-state evidence: `clean-regate-test.json`. Final hash audit: `verification.json`.
