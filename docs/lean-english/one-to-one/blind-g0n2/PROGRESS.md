# Phase B progress

Status: **DONE — 8/8 comparisons EQUIVALENT; 8/8 witnesses PASS.**

Time: initial inspection/compilation began approximately 2026-10-13T04:09:45Z; typed freeze was 2026-10-13T04:10:31.055431+00:00; completed 2026-10-13T04:20:08.913460+00:00 (approximately 10.4 minutes).

Done:

- Verified all eight Phase A hashes from back/BACK-HASHES.json.
- Compiled every back file as written; all returned exit 0, without repairs.
- Saved identical typed files and their SHA-256 manifest before opening original declarations.
- Recorded empty compile-fix diffs and original compile logs for every claim.
- Inspected the eight original declarations and relevant model/checker definitions.
- Saved exact frozen Back bodies, source signatures, pointwise conclusion comparisons and concrete witnesses.
- Passed eight statement checks and sixteen separate deterministic Claim/Witness gates.
- Kept the supplied deterministic gate and all its banned-token and axiom checks unchanged; documented runner relocation/glob adjustments.
- Wrote per-claim verdicts, hostile readings of all Does NOT say clauses, replacement sentences and ambiguity analysis in RESULTS.md.
- Implemented regate.py; missing-input checking returned failure (exit 1).
- Cleared prior gate receipts and transient directory, then re-gated all eight claims and witnesses from a clean receipt state (exit 0).
- Verified regating preserved every saved statement/proof hash, all back/typed byte identities, and receipt hashes of gate, runner, regate, input files and logs.

Not done: **none within the requested Phase B scope.**

What could not be done: **nothing required for this run.** Runtime authenticity, completeness, database/SQL refinement and sink behaviour are excluded by these model claims; they were not certified. Initial comparison-proof failures (namespace lookup, unfolding a Witness definition for decide, and concrete role proofs) were repaired in the new proof files. No back translation was altered.

All authored files are under this directory. No ControlStack source was edited; no git command or download was run. The only English material read was the authorized input batch and Phase A files; only the three authorized gate helpers were read elsewhere under docs/lean-english.
