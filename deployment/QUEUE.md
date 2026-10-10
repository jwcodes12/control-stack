# Deployment R2 queue

Source: `/var/tmp/sol-eval/HANDOFF-SOL-TO-R2.md`. This supersedes the earlier follow-up.
Tier 1 base: `a3bab7574e477f1ce7e130a7f81b845267efd99e`, draft PR #45, 25 CI successes / 2 expected skips.
No merging. Frozen artifacts and scenario statuses remain unchanged.

ID | status | evidence path or reason
---|---|---
T1.1 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.2 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.3 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.4 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.5 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T1.6 | DONE | ControlStack/Deployment/Contracts.lean; lean-build-attempt2.txt PASS
T1.7 | DONE | deployment/runs/tier1/differential.json: 26 fixtures + 250 mutations, zero differences, 276 kernel certificates
T1.8 | DONE | deployment/runs/tier1/monotonicity.json: 520 seeded strict additions, zero false improvements
T1.9 | DONE | ExtractionFaithful and ProtocolRefinement in Contracts.lean; claim/status/report updated
T1.10 | DONE | Existing tested mount/verdict regression in tools/test_deployment_slice.py and deployment-evidence/matrix/
T2.1 | DONE | deployment/runs/tier2/build/image-pin.json; offline imported cstack-r2 image, builder hash, no setid entries; first build argument error corrected
T2.2 | DONE | containers-attempt1: actual compose up, deployment/collect_docker.py, raw daemon pins, shared z labels with SELinux limits recorded
T2.3 | DONE | containers-final/clean/final: two distinct agents, two own-sink bodies, shared cap 2
T2.4 | DONE | containers-final: writable sink and UID confusion SUCCEEDED; replay/concurrent overspend/direct egress BLOCKED; exact outcome labels
T2.5 | DONE | containers-final/crash-retry and halt-inflight: actual KILL, unknown-commit gap, two dedup retries and fresh restart scan; HALT serialization
T2.6 | DONE | containers-final/drift-uid/drift: actual UID 23705 versus pinned 23701; DRIFT and UNASSURED
T2.7 | DONE | deployment/TIER2-AGREEMENT.md: seven safe cases; raw-byte/SQLite checker and cleanup pass
T3.1 | DONE | deployment/normalize.py; actual YAML test; raw/version/canonical provenance preserved
T3.2 | DONE | 44 generated fixtures; unsupported features UNKNOWN; dangerous fixtures never launched
T3.3 | DONE | deployment/scan.py and actual symlink tests; unresolved source UNKNOWN; host custody guard
T3.4 | DONE | nine stopped image exports; baked source/principal policy, USER, setid and entrypoint guards; final seven safe cases
T3.5 | DONE | canonical IR/bundle key-order/whitespace test; nine actual image semantic observations identical
T3.6 | DONE | security_ir/schema-v0.1.json, migrate.py and strict migration/unknown-field tests
T4.1 | DONE | ControlStack/Deployment/R2Contracts.lean deployment_broker_safe; joint quota/history, lagging publication, explicit refinement; r2-contracts-build.txt PASS
T4.2 | BLOCKED | Literal full-Accepted monotonicity is false: three kernel-checked writer-removal countermodels. Path-safety monotonicity proved with fixed bindings; retain usefulness rules.
T4.3 | DONE | accepted_no_avoided_path via explicit closed-set certificate; path_edge_subset and accepted_path_safety_monotone; standard axioms
T4.4 | BLOCKED | Three concrete Tier 2 replay compilations failed; final unsolved s0.halted=false / lease-cap guards. Generic indexed_receipts_sound passes; no concrete replay claim. See transcript-prototype-attempt3.txt.
T4.5 | DONE | contract-witnesses.json: 16 fixed contracts, 45 standard-axiom declarations; useful initial-to-release model trace; falsifying controls; CI mandatory checker
T5.1 | DONE | deployment/plan.py; read-only RFC 6902 patch, redacted human diff, separately reviewed host actions and precise capture/custody residuals
T5.2 | DONE | 44 static fixtures; 44 kernel certificates; 36 prospective finite-model acceptances, eight named residual cases; synthetic DECLARED facts never runtime evidence
T5.3 | DONE | Defensive-only: deployment/runs/tier5/remediated; originals archived Tier 2; two repaired live configurations, four honest completions; raw inventory/custody/SQLite/byte checks and tamper controls PASS. No new denial experiment.
T6.1 | TODO | Not yet started; tier order applies
T6.2 | TODO | Not yet started; tier order applies
T6.3 | TODO | Not yet started; tier order applies
T7.1 | TODO | Not yet started; tier order applies
T7.2 | TODO | Not yet started; tier order applies
T7.3 | TODO | Not yet started; tier order applies
T7.4 | TODO | Not yet started; tier order applies
T8.1 | TODO | Not yet started; tier order applies
T8.2 | TODO | Not yet started; tier order applies
T8.3 | TODO | Not yet started; tier order applies
T8.4 | TODO | Not yet started; tier order applies
T8.5 | TODO | Not yet started; tier order applies
T8.6 | TODO | Not yet started; tier order applies
G1 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G2 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G3 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G4 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G5 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G6 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G7 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G8 | GATED | Owner/resource prerequisite listed in handoff; not attempted
G9 | GATED | Owner/resource prerequisite listed in handoff; not attempted

Tier 1 local checks: exact-fixture Lean + full differential 2 PASS (362.740s); slice 13 PASS; runtime 17 with 2 host-Landlock skips; evidence 3 PASS; generated registry/catalog/overview/results/ledger/trust-root checks PASS. Frozen EgressGate SHA remains b491ec0accf6be75e7355667012b173760c5278b7180a31f4c4990ffad9f2af6. Final-head CI pending; no R2 claim.

Tier 1 CI attempt 1 at 64498eb: source-fidelity FAIL because its frozen-evidence guard matches every /evidence/ directory, including new deployment logs. Relocate only the newly added R2 logs to deployment/runs; retain the guard and every frozen artifact unchanged. Exact failure in deployment/runs/tier1/ci-source-fidelity-failure.txt.

Tier 1 exit: 08ce227b502f6b34e405804743b9f1d0f4b0b839, 25 CI SUCCESS + 2 explicit SKIPPED, PR #45 draft/open. Receipt: deployment/runs/tier1/ci-receipt-08ce227.json. Tier 2 branch sol/r2-tier2 is stacked on that exact tip. Historical container image/entry pins copied before the new image build so prior evidence remains independently checkable.

Tier 2 draft PR #46: https://github.com/jwcodes12/control-stack/pull/46, base sol/deployment-slice-20261010. Static fixture tests 13 PASS and historical archive checker 3 PASS after shared z labels and new offline image pins. The live collector is deployment/collect_docker.py.

Tier 2 first real run: seven safe cases PASS; independent raw inventory/SQLite/byte checker PASS. Self-review adds a fresh scan after receiver restart and stricter ownership, nonregular-sink and cleanup guards; final seven-case run is in progress. No dangerous fixture launched.

Tier 2 final local run: seven safe cases PASS; 26 fixtures + 250 seeded differential still zero differences; 520 additive regressions PASS; fixture --check PASS. Final archive replay/tamper checks and nine kernel certificates recorded under deployment/runs/tier2. Self-review in deployment/reviews/tier2-self-review.md. Final-head CI pending.

Tier 2 exit: a94813cc9a73400f1328f26b4af12da0636aef1f, 19 CI SUCCESS + 2 explicit SKIPPED, PR #46 draft/open. Receipt: deployment/runs/tier2/ci-receipt-a94813c.json. One pre-existing SC-01 cache probe failed to execute its encoder/decoder; unchanged failed-job rerun passed. Raw failure: deployment/runs/tier2/ci-viability-attempt1.txt. Tier 3 is stacked on that exact tip.

Tier 3 local exit: final fresh seven-case run PASS; nine archive kernel certificates; nine scanner tests including archive relocation/tampering PASS; 44 fixtures + 250 mutations zero differences; 520 monotonic mutations PASS. First replay after principal-policy guard failed with UID-collision IR differs; retained, then recollected final run. Self-review: deployment/reviews/tier3-self-review.md. Draft #47; final-head CI pending.

Tier 3 exit: 8c7ff7288b67b8ef46675fe558ba12d8edda04bb, 19 CI SUCCESS + 2 explicit SKIPPED. Receipt deployment/runs/tier3/ci-receipt-8c7ff72.json; fresh local checkout nine scanner tests PASS. Draft #47 remains open. Tier 4 branch sol/r2-tier4 is stacked on that exact tip.

Tier 4 local exit: TrustedBroker/path contracts and witness module PASS; fixed 16-contract / 45-declaration package PASS; registry, source-normalized catalog, overview, results, ledger and trust-root checks PASS. T4.2 literal theorem BLOCKED by checked countermodels; T4.4 concrete replay BLOCKED after three compilation failures. No installed proof depends on sorryAx. Self-review deployment/reviews/tier4-self-review.md. Final-head CI pending.

Tier 4 exit: 379913094b1fb9c3c1eee7846424d55cf6724737, 24 CI SUCCESS + 2 explicit SKIPPED. Exact-head receipt deployment/runs/tier4/ci-receipt-3799130.json. #48 remains draft/open; T4.2 and T4.4 remain explicitly BLOCKED. Tier 5 branch sol/r2-tier5 stacks on that exact tip.

## Defensive-only continuation — John via agent-bus message #2

T5.3 uses archived Tier 2 originals and launches only remediated configurations. Tier 6 is static review of misconfigured Compose deployments, with no exploit code or attack payloads. Tier 7 is preregistered attribution of existing Tier 2 outcomes plus honest tasks; the original four-arm attack evaluation is GATED because the owner has no cyber-permissive access tier. If a task is flagged again, record its exact error as GATED and move on. T4.2 and T4.4 remain BLOCKED. Tier 8 remains required. Existing CI live negative boundary job is explicitly skipped under this scope; archive validation continues, and skipped work is never counted as passed. No merging.

Tier 5 local exit: planner five tests PASS; 44 prospective kernel certificates, 36 model accepted and eight named residual cases; two remediated live configurations and four honest completions PASS. Independent archive and two tamper tests PASS; resources removed. Original = archived Tier 2 evidence, no original bypass rerun. Self-review deployment/reviews/tier5-self-review.md. Final-head CI pending.

Tier 5 CI attempt f1fbf63: fixture job FAIL because planner inferred an archived absolute fresh-input path unavailable on CI. Preserve the raw failure; infer local sibling inputs and compare all pinned IR content while normalizing only hash-identical known source labels. Add relocation and modified-observation rejection controls. No evidence files are edited. Final corrected-head CI pending.

Tier 5 fresh checkout: six planner tests PASS; remediated archive replay FAIL on relocated trusted-source labels. Reuse the same hash-pinned known-artifact source-label normalization in the independent checker; retain both failure and corrected results. No evidence bytes altered.

Tier 5 corrected fresh local checkout: six planner tests and two remediated archive/tamper tests PASS. Source relocation normalization preserves known artifact hashes and every other IR field. Corrected final-head CI pending.

Tier 5 final review tightened read-only output protection: saved observation directories and pinned trusted-source inputs cannot be used as plan output. Relocation test also verifies a refused observation overwrite leaves all bytes intact. Re-run static checks; no additional container or bypass run.
