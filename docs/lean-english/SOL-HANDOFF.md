# Handoff: Sol's English <-> Lean one-to-one work (state at 2026-10-11 ~21:00)

**Read this first: do a reuse pass BEFORE continuing Sol's check.** Owner's decision: before more of the one-to-one check is done, go through all the
Lean claims and make sure we **reuse existing lemmas/Lean instead of reinventing**. Reason: many of the 187 claims are instances of a few shared cores
(`ControlStack/Core/Gate.lean` is imported by 27 files, `Core/Authenticated` by 7, plus `AuthenticatedLog`, `CheckedTrace`, `AntiRollback`), and some lemmas may already
be proved in `~/research/alignment-contrib/lean/StabilityDebate`, `~/research/control-tree` or the `proofledger` ledger. Checking English for statements that should
be deduplicated or replaced by an existing lemma is wasted work, and the English changes if the Lean does.

## What exists
- Plain-English statements: `docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md` (overview, 187 claims) and full blocks `docs/lean-english/part-g0..g7.md` (Sonnet, from the Lean).
  Only ~9% of the 2,222 registry declarations are covered; supporting lemmas are not translated.
- Protocol: `docs/lean-english/ONE-TO-ONE.md`. Sol's instructions: `/var/tmp/sol-eval/HANDOFF-SOL-ONE-TO-ONE.md` (G0) and `...-B.md` (G1-G7, strict blind).
- Sol's inputs live in `docs/lean-english/sol-input/` (git-excluded; they contain **12 planted-wrong English statements** as canaries; the key is in the orchestrator's
  scratch dir, not in the repo). Do not commit `sol-input/`.

## Results so far (G0, the 26 deployment-stack claims; `docs/lean-english/one-to-one/RESULTS.md`)
19 equivalent, 2 weaker, 3 stronger, 2 undecided; 26 claim and 26 witness gate checks passed; extra provenance invariant proved
(`ProvenanceDraft.lean`, not yet integrated into `ControlStack/`). Canaries: 5 of 6 flagged cleanly, 1 (`halted_absorbing`, stronger-but-true) passed with a note.
Real findings: `Accepted` identity is "iff" (English said "only if"); `runtime_trace` English omits the ten-step ordering; corrections are listed in RESULTS.md.
**Caveat (Sol's own):** the G0 pass was not strictly blind; typed Lean was written after reading the source.

## G1-G7 (161 claims): requested, not delivered
Task sent 20:17 (strict-blind, flagged claims first, list in `HANDOFF-SOL-ONE-TO-ONE-B.md`); stop-after-current-eval sent 20:44 on the owner's instruction. Sol read both;
at the time of writing no result files existed under `docs/lean-english/one-to-one/` after 18:32 and no bus reply had arrived. Treat G1-G7 as **not started** unless
`RESULTS-G1-G7.md` / `PROGRESS-G1-G7.md` exist.

## Resume plan
1. **Reuse audit (first; orchestrator or any agent):** for every claim, one row: the shared core it instantiates, an existing lemma (repo, Mathlib/Std, other repos) that already
   states it, or `unique`. Mark duplicates (`AuthInstancesA/B`, `*Refinement`, `*Liveness` repeat three generic patterns: gate invariant, authenticated adversary, refinement transfer).
   Output: `docs/lean-english/REUSE-AUDIT.md`. Decide what is deleted, restated as an instance, or imported from another repo.
2. Simplify the Lean accordingly (named fields for `Allowed`/`Accepted`, integrate the provenance invariant, decide T4.2); regenerate the English blocks that changed.
3. Re-run the one-to-one check on the deduplicated set, **strictly blind** (write and hash the typed `Back` before opening the original theorem), flagged claims first, canaries
   refreshed. Compare conclusions under the same hypotheses (two true closed theorems are trivially equivalent).
4. Promote "one-to-one verified" badges only from gate-passing, strictly blind results.
Rules unchanged: defensive static work; write under `docs/lean-english/one-to-one/`; no edits to frozen paths; no git operations by Sol; the proofledger adapter is `run_gate.py` in that folder.
