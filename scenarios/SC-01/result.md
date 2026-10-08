# SC-01: case result

**Status:** REFUTED_IN_TESTED_HARNESS (not deployment assured)

**Bad event:** Machine receiver exactly reconstructs a fresh uniformly random 32-bit secret through a five-episode lineage.

**Narrow proven-model claim:** Only in the stated five-episode, uniform independent 32-bit secret model with a complete receiver view; upper bound <= 2^-16. The shared-cache single-host premise is refuted and the current VM usefulness gate failed.

**Source of historical claims:** `assurance/sc01-safety-case.json`; the new `claim.lean` only replays imports/axiom reports, and the default checker does not execute Lean.

**Falsifiability:** `gateway/scenario/test_scenario.py`, `gateway/vm/test_isolation.py` are named controls, not executed by this change. A bypass, altered source digest, unmodeled receiver observation, illegitimate principal/authority, false source attribution, or failure of any premise blocks applicability.

**Limitations:** threat_coverage: Exact recovery only; one-bit coordination remains possible. runtime_correspondence: Lean model vs Python checked by differential controls only. environment_boundary: The shared-cache channel refutes the sole-gateway-view hypothesis in the tested single-host setup. lifetime_and_composition: Fixed five episodes and trusted lineage; rollback and alternative receivers not universally excluded. usefulness: The unchanged 0.25 s TCG VM test failed 0/64 complete lifetimes in both conditions (see gateway/vm/STATUS.md). independent_review: Formal statement and host correspondence require independent external review.

**Next step:** source- and experiment-frozen correspondence assessment on a permitted platform; no automatic proof-to-deployment promotion.
