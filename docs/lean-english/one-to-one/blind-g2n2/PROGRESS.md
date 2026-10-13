# Phase B progress

Done: 8/8 back hashes verified; 8/8 back files compiled unchanged; typed copies and hashes frozen before original reads; 8/8 declarations compared; 8/8 comparison Claims and 8/8 Witnesses passed the unchanged deterministic gate; RESULTS.md completed with corrections, ambiguities, pointwise scope, and hostile readings of every exclusion; standalone regate.py verified from a state with no current receipts or gate scratch.

Not done: none of the requested claims or artifacts remains unfinished.

Time: typed hash freeze 2026-10-13T04:29:51.868948+00:00; final clean gate and integrity verification 2026-10-13T04:41:39.552385+00:00. Elapsed since the freeze: 708 seconds (11.8 minutes), plus the initial compilation phase.

Verdicts: seven EQUIVALENT, one ENGLISH_STRONGER (claim 4, at the output-predicate level). No UNDECIDED, NOT_FORMALISABLE or unfinished claim.

What could not be done / limits: no counterexample on the actual forged12 execution exists in this run; the gate verifies its stronger whole-state conclusion. The claim-4 strength distinction is between observation predicates, with a counterexample on an arbitrary returned state, as explicitly explained in RESULTS.md. None of the residual real-world deployment conditions was verified. The gate establishes Lean proofs about the model only.

Failures resolved: the first comparison-proof attempt failed elaboration for claims 4 and 5 (explicit definition unfolding and an Inv name qualification). Failed receipts and their exact failed inputs are archived under gate-attempts/first/. Back files required no repair.

Reproduction: run `python3 docs/lean-english/one-to-one/blind-g2n2/regate.py` from the repository root. The clean run exited 0 with 16 passing receipts; saved non-receipt files were unchanged. The script exits nonzero if any expected input or gate check fails.

Scope: no git commands; no ControlStack edits; all authored files are under docs/lean-english/one-to-one/blind-g2n2/. Only the authorized English batch, back files and gate helpers were consulted under docs/lean-english/ outside the new Phase B outputs.
