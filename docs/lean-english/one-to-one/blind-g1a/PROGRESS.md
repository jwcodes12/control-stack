# Blind G1a Phase B progress

Status: DONE — 9/9 claims, 9/9 comparison gates, 9/9 separately targeted Witness gates.

Started approximately 2026-10-13 03:52 UTC. Finished 2026-10-13 04:04:27 UTC (approximately 12.5 minutes).
Typed copies frozen before opening originals: 2026-10-13T03:54:13.745756+00:00.

Done:
- Checked all nine Phase-A hashes and compiled every back file as written.
- Wrote byte-identical typed copies, SHA-256 manifest and nine no-repair records before reading original declarations.
- Inspected the nine original signatures and relevant model definitions.
- Proved pointwise comparisons, including the probabilistic-to-deterministic strategy extraction for claim 3.
- Passed the unchanged deterministic gate for all comparisons and separately for all Witness targets.
- Audited every “Does NOT say” item and wrote replacement sentences and ambiguities in RESULTS.md.
- Preserved failed gate attempts, current gate logs, hashes and receipts.
- Checked all current artifacts against their receipts; checked original module hashes remain unchanged since inspection.

Not done: none of the requested nine comparisons, witnesses or report outputs remains unfinished. No claim is UNDECIDED.

What this run could not establish: real sandbox isolation, credential separation, semantic harmlessness, output independence in a deployment, exact installed rules, kernel/runtime correspondence, host test results, or empirical scope of named world assumptions. These are outside the supplied theorem statements and the authorized reading scope; no excluded English documentation or deployment evidence was read.

Operational limits: the umbrella Mathlib module was not built, so PL_IMPORTS uses the already-built Mathlib.Tactic. No build/download was needed. No back repair, gate-security modification, ControlStack edit, git command, or external publication occurred.

Reproduce: `python3 docs/lean-english/one-to-one/blind-g1a/gate_all.py` from the repository root; then run `python3 docs/lean-english/one-to-one/blind-g1a/verify_final.py` to check current receipts and hashes. The copied runner's original ROOT expression is retained through the driver, as explained in RESULTS.md.
