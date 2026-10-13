# Phase B progress

Done at 2026-10-13T10:48:15.118271+00:00 (UTC). Work began approximately 2026-10-13T10:30:00Z; exact compile/hash freeze: 2026-10-13T10:31:42.020382+00:00.

- Done: Phase A manifest verified; all 13 back files compiled unchanged; all 13 typed hashes frozen before opening originals; per-claim no-repair records and compile logs saved.
- Done: all 13 original declarations inspected; source-signature hashes saved; imported original types checked in the gate; back/original encoding checks gated.
- Done: 12 pointwise equivalence proofs, plus claim 6's limited diagnostic counterexamples. Every saved Claim and every Witness passes its separate deterministic gate (26 target checks).
- Done: hostile English review, per-claim exclusion assessment, replacement sentences, ambiguities, results table and supporting files.
- Done: clean-state regate test from the repository root, with all receipts and the empty gate scratch directory removed first. Exit 0; saved inputs unchanged; receipts match current statement/proof/gate hashes. See clean-regate.log and clean-regate-verification.json.

Not done / could not certify: claim 6's required one-to-one verdict. Its two closed computations are true but describe different observations. Counterexamples to their generalized output predicates do not refute the fixed trace. Accordingly its verdict is UNDECIDED; the diagnostic Claim receipt is not an equivalence or fixed-trace difference receipt.

No other claim is unfinished. No empirical kernel, credential, meter, crash-window or runtime-latency premise was independently verified; those are outside the specified formal comparison. No git, downloads, external research, edits to ControlStack, or reads of forbidden English/comparison files were performed.

Re-gate: `python3 docs/lean-english/one-to-one/blind-g7n2/regate.py`. This reuses saved statements/proofs, writes receipts only (with disposable gate scratch files), and fails if any statement, claim or witness check fails. Exit 0 does not imply an EQUIVALENT verdict for the diagnostic claim 6.
