# Progress

**Complete.** All eight claims compiled after import-only repairs, compared with their originals, and assigned final gated verdicts. Claim 1 is ENGLISH_STRONGER; the other seven are EQUIVALENT. Eight comparison/counterexample gates and eight separate witness gates passed. RESULTS.md contains corrections and the per-claim over-reading audit.

Started: 2026-10-13 03:32:11 UTC. Finished: 2026-10-13 03:44:00 UTC. Total elapsed: 11.8 minutes.

- Compilation, repair diffs, and hash freezing: 03:32:11–03:33:48 UTC, about 97 seconds. Every bare back file failed for absent imports; every repaired file compiled. No semantic repair was made.
- First original-source read: 03:33:58 UTC, after the typed hash file existed. Source excerpts and hashes are in originals/.
- Source comparison, directional proof, counterexample, theorem and witness gates: approximately six minutes after first source inspection. Final report and receipt/hash audit used the remaining time.
- No old comparisons or other forbidden lean-english documents were read. No git command, download, ControlStack edit, or write outside blind-v1 was performed.

Retained failures: the first comparison gate run exposed missing namespace opens in several comparison proof files, repaired only in those new supporting proofs. Claim 1's initial finite checks failed to synthesize Decidable for the entire blind predicate; unfolding alone also failed. The final counterexample uses an explicit identity contradiction, and its clean witness checks each group separately. Historical statements, proofs, logs and receipts are under attempts/ with matching hashes. These failures did not alter the frozen typed blind statements. Exploratory Lean files remain alongside the final supporting files; their failed examples are not verdict evidence.

Gate integrity: the local helper is byte-identical to the supplied helper. Driver relocation requires parent index 4 rather than 3 to preserve the project root, and the glob is b1_*; all security checks remain intact. The supplied driver's historical receipt field gate_unmodified=false describes its existing imports-enabled wrapper; security_checks_unchanged=true and helper identity are separately recorded. No claim gate passed with sorryAx or a nonstandard axiom.

Final verification: FINAL-AUDIT.json confirms all sixteen final receipts passed, match the final statement/proof/helper hashes, and have PASS logs; original and repaired blind hashes match; repair bodies are unchanged; historical attempt receipts match their preserved files.

Remaining work: none within this batch. Not attempted or established: real-world extraction faithfulness, authenticated runtime history, Python/kernel correctness, deployment behavior, or a global node-ID uniqueness property. Those are outside this statement-comparison task. No EQUIVALENT verdict was assigned to claim 1; its reverse implication is refuted by the gated instance.
