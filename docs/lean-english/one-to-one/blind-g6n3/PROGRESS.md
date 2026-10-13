# Phase B progress

Done: 6/6 original Back compilations, no repairs; original Back hashes verified; identical typed copies and hashes frozen before original declarations were opened; 6/6 pointwise comparisons; structural links to frozen Back definitions and copied original signatures; 6/6 separately gated non-vacuity witnesses; hostile English audit; proposed corrections; final clean-state regate and receipt/hash validation; RESULTS.md and all supporting files.

Verdicts: all six principal Back/original statements EQUIVALENT. All six comparison targets and all six witness targets passed the unchanged deterministic gate. Claim 6's separately gated witness also proves that the auxiliary strict-weakening assertion is not a general predicate implication.

Not done: none within the requested scope. No UNDECIDED or unfinished claim.

Time: typed freeze 2026-10-13T05:40:45.057356+00:00; completed 2026-10-13T05:54:51.929069+00:00; elapsed after blind compilation/freeze 0:14:06.871713. The short initial read/compilation interval precedes that freeze timestamp.

Verification: `python3 docs/lean-english/one-to-one/blind-g6n3/regate.py` ran from the repository root with prior receipts, gate scratch and Python cache removed; exit 0; 6 statement checks, 6 claims and 6 witnesses passed. It persisted only receipts. All Back, typed, statement and proof hashes match their saved manifests. Gate helper matches the permitted original byte-for-byte. The only runner path adjustment beyond imports/glob is the extra directory level in ROOT resolution, documented in runner-relocation.txt.

What could not be certified: the full auxiliary English assertion “strictly weaker” cannot be certified as written; a counterexample was instead certified and replacement wording provided. These theorem equivalence receipts do not prove unconditional real-network fairness, elapsed-time guarantees or the behavior of an external deployed implementation. Such claims are outside the supplied theorem statements.

No project source was edited. No git command or download was run. Existing comparison results and other English material were not used. All authored outputs are inside blind-g6n3.
