# Phase B progress

Done: **10/10 claims**; all EQUIVALENT. **20/20 independent claim and Witness gates passed.**

- Verified all Phase-A back hashes, compiled all ten back files unchanged, and froze byte-identical typed copies and their SHA-256 hashes before opening originals.
- Recorded ten no-repair diffs and the original compile logs.
- Inspected and saved the ten original declaration types and source hashes.
- Proved conclusion iff under shared hypotheses, including tuple, singleton-log, and causal trace-origin bridges; saved and froze all statement/proof files.
- Copied and relocated the runner using the supplied unchanged gate helper; banned-token and axiom checks were not modified.
- Ran regate.py from the repository root after deleting all receipts, with no generated Lean gate files present. Exit code: **0**. All ten statement checks, ten claim targets, and ten Witness targets passed; receipts were recreated.
- Audited final receipt/input hash consistency, script syntax, original compile exit codes, and empty gate temporary directory.
- Wrote RESULTS.md with the verdict/receipt table, per-claim hostile reading, English replacements, and ambiguities. No English input files were edited.

Not done: **none of the requested claims or deliverables**. No failed final proof, UNDECIDED claim, or unfinished comparison remains.

Time: started approximately 2026-10-13T05:58:00Z (minute precision); finished 2026-10-13T06:16:07.359746+00:00; elapsed approximately 18.1 minutes. Typed hashes frozen at 2026-10-13T05:59:25.162789+00:00. Final re-gate stdout is in clean-regate.txt.

What could not be established: this task does not prove real runtime/Python correspondence, real auditor perception or judgment, platform identity authenticity, collision resistance of a real digest, or a real bank's authentication/idempotence. Those remain outside the compared Lean conclusions. Phase-A blindness is taken from the owner's instruction; this run verifies the supplied files' hashes and its own compile-before-original ordering.

Scope: no git commands, downloads, sub-agents, ControlStack edits, or writes outside docs/lean-english/one-to-one/blind-g6n1/. No old comparison results or other lean-english content were used. The relocated runner requires adjusting repository-root and helper-resolution paths as part of relocating its output; runner-relocation.diff records these changes transparently. The deterministic gate implementation itself is unchanged.

Recheck:

```sh
python3 -B docs/lean-english/one-to-one/blind-g6n1/regate.py
```

regate.py checks frozen inputs and every claim/Witness with the deterministic gate, rewrites only their receipts, and exits nonzero if any check fails.
