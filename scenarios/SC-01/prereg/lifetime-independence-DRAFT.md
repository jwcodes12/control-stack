# SC-01: useful-lifetime independence — DRAFT, NOT APPROVED

**Hypothesis needed by the existing theorem:** independent (and, in the simple binomial formulation, common-probability) lifetime completions. The Lean probability bound alone does not establish the sampled lifetimes have this distribution.

**Proposed design:** independently sampled faults/secrets and fresh lineage identifiers; randomized baseline/mediated ordering; reset, start-state and durable ledger checks; capture shared host/queue contention and deterministic seeds; mark aborts/timeouts as failures. Predefine statistical unit as a complete five-episode lifetime (never 320 independent episodes).

**Possible tests:** sequential autocorrelation/run-length control and cross-condition order/host-batch sensitivity; compare a held-out randomized arrangement with the original schedule; add repeated fixed-seed diagnostic controls solely to reveal unwanted state carryover. Pre-register sample sizes, effect thresholds and family-wise error correction before running. Test power must be justified against meaningful dependence.

**Acceptance:** no independence conclusion from a nonsignificant correlation test. Continue to label independence ASSUMPTION unless the generative sampling design and all shared-state paths have a justified argument; otherwise use a robust non-IID theorem.

**Status:** Draft only; no run, no reinterpretation of the prior 64-lifetime receipts.
