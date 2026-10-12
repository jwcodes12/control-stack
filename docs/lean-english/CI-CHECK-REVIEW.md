# PR #56: CI optimization adversarial review

**Model-written/model-reviewed; no independent human review.** This is a review of the workflow source and new negative-control checks, not a measurement of hosted-runner cache performance or proof of operating-system effects.

## Cancel superseded and cache

PR-only `concurrency` cancellation can terminate **old** PR-head workflows; it does not certify the latest head. A workflow being cancelled or skipped is not a passing result. Required checks must pass on the exact commit under review. The Lean cache key includes `github.sha`, pinned toolchain, Lake manifest and lakefile; restore-key reuse may supply old compiled artifacts, but full `lake build` and axiom checks remain required. The cache is a build acceleration, not an authority for theorem correctness. Cache poisoning or untracked toolchain behavior is not excluded by this test.

## Batched certificate checks

Originally the batch checker counted nine axiom-report messages per fixture, but **did not match each report to its expected theorem**. A duplicate or substituted printed report could preserve the count while omitting one fixture's output. `check_axiom_reports` now matches exact occurrence counts of the six shared contract names per fixture plus `facts_i`, `contract_checked_i`, and `one_use_checked_i`. It still permits only `propext`, `Quot.sound`, `Classical.choice` and rejects `sorryAx`.

The new `tools/test_deployment_fixture_batch_negative.py` is executed inside the pinned-toolchain `deployment-release` kernel job. It asserts that:

1. A *real Lean* theorem claiming `¬ Accepted clean` fails compilation (`clean` is `Accepted`).
2. Lean reports a deliberately introduced new axiom for another theorem, and the batch parser **rejects** its non-standard dependency.
3. A synthetic same-count substitution of a per-fixture report is rejected, not treated as a complete batch.

This tests the certificate checker and its log parser; it does not prove that the fixture projection from Python is faithful or that the actual runtime matches `IR`, and it does not independently benchmark runtime reduction. Preserve all source-pin and frozen-input checks. No change is made to production trusted_stack code.
