# Phase B progress

Done: all ten claims audited; all ten Phase A hashes verified; all ten back files compiled as written; ten import-only repairs recorded; all typed files compiled and hashed before originals were opened; eight pointwise equivalence verdicts certified; two conservative UNDECIDED verdicts documented with certified directions and conclusion-predicate diagnostics; ten substantive non-vacuity witnesses certified; English corrections and over-reading audits written; reproducible re-gater saved.

Not done: claim 4's Back-to-Orig implication for the actual halted run, and claim 8's Back-to-Orig implication for the actual fixed trace. Neither has a certified iff. The semantic diagnostic counterexamples concern symbolic observations and do not establish counterexamples to actual deployed traces. No strict ENGLISH_WEAKER, ENGLISH_STRONGER or DIFFERENT verdict is asserted from those diagnostics. The truth of two complete theorems was not used to manufacture equivalence.

Time: earliest retained as-written compiler log 2026-10-13T05:40:36.334225+00:00; typed-hash freeze 2026-10-13T05:41:13.039783+00:00; final validation 2026-10-13T05:56:40.412534+00:00. Recorded execution window since the earliest compiler log: 964.1 seconds (excludes initial setup/read time).

Verification: `python3 docs/lean-english/one-to-one/blind-g6n2/regate.py` ran from the repository root after removing all twenty current receipts and the empty gate scratch directory. Exit code **0**. All **10 claim gates and 10 separately targeted Witness gates PASS**. The gate helper is byte-identical to the authorized original. Final validation matched every current receipt to the saved statement/proof bytes, checked all back/typed/final proof hashes and original source hashes, checked report links, and found no residual temporary Lean check file.

What I could not do: certify a non-shortcut same-run reverse implication for claims 4 and 8. No operational, liveness, informed-consent, real-runtime correspondence or identity-authenticity claim outside the given Lean declarations was established. Those limits are documented in RESULTS.md, with replacement English where needed.

Constraints: no original source edited; no git run; no download; all output writes confined to this directory. Initial failed gate receipts remain under gate-attempts; final verdicts use only the top-level passing receipts.
