# Plan: making the project approachable for a human researcher (roadmap item, not started)

Status: **planned, deliberately deferred.** Order of work agreed with the owner: (1) merge the open PRs, (2) simplify the Lean, (3) the
human- and resource-gated work (independent review, real agents, other platforms), (4) this plan. Nothing below is implemented except
the plain-English statement set it builds on (`docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md`, `docs/lean-english/`).

## Why
There are about 187 headline Lean claims (2,222 declarations in all). A researcher cannot review them one by one. Most are instances of a
few patterns, so review effort should go into the patterns, the guards of each instance, and the premises.

## Deliverables, in order
1. **Pattern pages** (about 3 pages): the shared shapes, each explained once with a tiny worked example: gate invariant over traces
   (`Core/Gate`, 27 files use it), authenticated adversary (`Core/Authenticated`, `AuthenticatedLog`), refinement of a concrete machine
   (`Core/CheckedTrace`, `*Refinement`), anti-rollback, quantitative bounds (covert channel, audit sampling), anchored logs (SC-27), the
   deployment verifier. Each scenario claim is then written as "instance of pattern P with guards G", so the pattern is reviewed once.
2. **Glossary** of recurring terms (lease, nonce, gate, HALT, refinement, anchor, TV distance, IR, extraction) with one line per Mathlib/Std
   fact that needs no further explanation (`List.Nodup`, `List.Sublist`, ...).
3. **Premise view:** each of the 29 premises in `ASSURANCE-LEDGER.md` linked to the claims that depend on it, so a reviewer can work premise by
   premise instead of theorem by theorem.
4. **Claim cards** (one per claim): plain statement; what it excludes; status badge (proved in model / premise / tested / one-to-one
   verified, taken from Sol's gate-checked verdicts in `docs/lean-english/one-to-one/RESULTS.md`); "to refute this, find ...".
5. **Counterexample gallery:** for each guard, the model run that fails without it (the negative-control theorems already exist).
6. **Reading paths:** 30 minutes (the map plus the deployment headline claim), 2 hours (the deployment stack), deep dive.
7. **Runnable demos:** a small `cstack explain` or Lean demo file showing a clean configuration accepted and the same with one writable
   mount refused, reusing the existing witnesses.
8. **Review kit:** checklist and a structured feedback template so reviewers' notes can be acted on.
9. **Readable Lean** (depends on the Lean-simplification step): named fields instead of long conjunctions, with proved equivalences.

## Reuse (to check before writing anything new)
- The repo's own cores (above) instead of per-scenario re-explanations.
- Mathlib/Std lemmas: glossary entries only.
- `~/research/alignment-contrib/lean/StabilityDebate`, `~/research/control-tree`, `~/research/proofledger` ledger: the covert-channel and adaptive-audit
  lemmas may already be proved there; cite or import instead of duplicating (not yet checked).

## Done when
A researcher unfamiliar with the repo can, in one afternoon, (a) say what each pattern guarantees, (b) list the premises the headline claim
rests on, (c) find the claim cards that depend on a premise they doubt, and (d) file structured feedback.
