# Sealed static configuration review

The separate `codex exec` author was given a public six-service reference-profile
specification. bwrap hid repository copies, the extractor, verifier, fixtures and
prior session history. The host filesystem was read-only; scratch and fresh private
Codex state were writable. Two startup failures and the unavailable author shell
tool are retained. File writing and checksum generation completed successfully.

The author sealed 25 new cases: five supported, twelve refuted, eight unknown.
Every selected runtime inventory is a hypothetical input, not a daemon observation.
Image/code correspondence and directory custody are given model hypotheses.
Labels and every authored file were committed at 481f56f before any scoring.
Checksums and the coordinator seal are mandatory regression inputs; byte changes
are rejected. Nothing relabels the frozen ground truth.

Phase | false model acceptances / 20 negatives | rejected / 5 supported | UNKNOWN / 25 | model plans accepted / 25
---|---|---|---|---
Raw authored inputs | 0 | 5 | 25 | 0
Known-code hypothesis instantiated, before order fix | 0 | 2 | 14 | 22
After inventory-order fix | 0 | 0 | 14 | 22

The author-facing interface omitted required trusted-source hash fields. Raw inputs
correctly fail closed. The explicit `--instantiate-known-code` evaluator option adds
actual local source digests to copied declarations under the already stated known-code
hypothesis. It does not edit sealed inputs, infer a scanner pin automatically, inspect
an actual image or create a runtime observation. The raw result is retained separately.
This adapter is an evaluator-interface correction, not a relaxed verifier rule.

The two remaining supported misses were mount-order comparisons: equivalent receiver
mount lists differed only in order. The fix was committed before rescoring. Sorting is
allowed only for unique mount targets with string source/target paths; all fields and
multiplicities survive. Ambiguous targets remain ordered. UID discrepancies, unlisted
writers and unsupported metadata still reject. A regression preserves extra facts and
repeated targets. The source-pin planner also names missing/drifted pins explicitly.

The final finite-model score has zero author-negative acceptances, zero over-rejections,
56% UNKNOWN, 22/25 prospective model plans and three plans with named residuals. Fifty
kernel certificates cover both original and prospective IRs. No model result establishes
actual image, source realpath, host custody, runtime completeness or protocol refinement.
MODEL_ACCEPTED is deliberately distinct from a live CONDITIONAL verdict. The corpus
covers restricted JSON finite extraction and planning; fresh Compose CLI normalization,
realpaths and image observation are exercised by the separate Tier 3 checks and archives.
It is not a held-out runtime or full fresh-scanner boundary test.

The plain Python baseline rejects 2/20 author-negative declarations and 0/5 supported
ones. It checks root UID, credentials, privileged/host namespaces, extra capabilities and
system/socket binds. It does not model role separation, writer paths, required writers,
selected-inventory correspondence or unsupported-feature completeness. ALLOW is a rule
result, not assurance. Actual OPA/Conftest is GATED; these results do not rank OPA generally.

Reproduce without container launches:

```
python3 tools/test_deployment_heldout.py
python3 tools/check_deployment_heldout.py --output /tmp/raw-static.json
python3 tools/check_deployment_heldout.py --instantiate-known-code --output /tmp/model-static.json
```

The JSON reports in deployment/runs/tier6 retain all case-level obligations, unchanged
author reasons, baseline findings, source digests, seal hashes and standard axioms.
The first raw and pre-order-fix results are preserved alongside the corrected result.
