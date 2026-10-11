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
T6.1 | DONE | deployment/heldout/tier6: 25 independent static cases (5 supported, 12 refuted, 8 unknown), labelled and hash-sealed before scoring; separate blinded codex exec; two startup failures retained
T6.2 | DONE | 25 sealed static cases; final 50 kernel certificates: zero false model acceptances, zero over-rejections, 14 UNKNOWN, 22 prospective model plans and three named residuals. Raw/interface and pre-order-fix scores retained; no runtime assessment.
T6.3 | DONE | declaration-only rules_baseline.py catches 2/20 author negatives and rejects 0/5 supported; scope limited, no OPA comparison claim; actual OPA GATED
T7.1 | DONE | New prereg/PREREG-DEPLOY-ARMS-v1.md and deployment/prereg-deploy-arms-freeze.json: nine archived episodes, fixed thresholds and honest timing gaps, frozen before attribution; retrospective, outcomes already known
T7.2 | DONE | attribute_archives.py: nine independent archive replays; literal outcomes, two observed bypasses, six explicit honest workflows and gaps retained; no new attack policies
T7.3 | DONE | Retrospective attribution metrics/H1-H4 PASS: six honest workflows, nine approved deliveries, one unauthorized file; monitor null, three unmeasured latencies; no four-arm result
T7.4 | DONE | Episodes and restricted Inspect-v2 JSON schemas, deterministic converter, four regression tests; official field reference pinned; actual SDK loader validation GATED
T8.1 | DONE | deployment/RELEASE-GATES.md: 11 gates PASS or PASS (scoped); independent review G1 open; exact-head CI in END-STATE.md
T8.2 | DONE | cstack demo; deployment/runs/tier8/demo-fresh-clone (fresh GitHub clone at 0f8f7b9, exit 0, all four stages PASS) and demo-dev-clone
T8.3 | DOING | .github/workflows/deployment-release.yml; live job always skipped on GitHub runners and asserted SKIPPED, never a pass; first run pending
T8.4 | DONE | deployment/schemas/{bundle,plan,demo}-v0.1.json; deployment/golden; tools/test_deployment_release.py 5 PASS (also in fresh clone)
T8.5 | DONE | docs/DEPLOYMENT-QUICKSTART.md (quickstart, platforms/versions, exit codes, claim ladder, threat model, TCB, lifetime); delegation added to unsupported scope in the claim
T8.6 | DONE | deployment/REVIEW-PACKET-R2.md; reproduction commands re-run PASS; trusted-path model review deployment/reviews/trusted-path-code-review-opus.md with dispositions
T9.1 | DONE | Versioned trusted-source pins: archive replays and image pins check their own historical source hashes (git blobs), so trusted_stack can change without invalidating Tier 2-8 evidence. Prerequisite for T9.2-T9.5
T9.2 | DONE | R2 broker profile without delegate/revoke_delegation (or a flag the scanner records); sink audit stays as evidence (review M1)
T9.3 | DONE | server.py: catch every exception per connection, bound nesting/frame size, total per-connection deadline, bootstrap only when the DB is absent, reject UID 0 and non-admin broker euid, HALT retry (review M2, L1, L2, L4-L6)
T9.4 | DONE | Supported profile requires no-new-privileges and cap_drop ALL for agents; scanner inventories security.capability xattrs; absence UNKNOWN (review M3)
T9.5 | TODO | Receiver reaps unmatched .pending-* under the DB lock; unit test for pre-link crash (review L3)
T9.6 | TODO | Re-run the non-bypass live cases (clean, concurrent-cap1, crash-retry, halt-inflight, drift-uid) and the demo on hardened code; regenerate pins; no bypass reruns (defensive scope)
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

Tier 5 exit: c0f5f4512557cfd42b5073f2e5c79afbaeafa8fd, 18 CI SUCCESS and 3 explicit SKIPPED; PR #49 draft/open. Receipt deployment/runs/tier5/ci-receipt-c0f5f45.json. Tier 6 stacks on that exact tip; no R2 completion claim.

T6.1 author attempt 1: Codex failed before authoring with read-only filesystem error initializing its in-process app-server. Preserve raw error; provide a fresh private writable Codex state directory under this clone, with no prior sessions or evaluator access. No corpus or evaluation produced.

T6.1 author attempt 2: bwrap could not execute the Codex binary because its .local/bin symlink points inside the now-hidden .codex/packages directory. Restore only read-only executable packages into the private state mount; repository/session history remains hidden. Attempt 3 will be the final startup attempt under the time-box.

Tier 6 corpus sealed: 25 cases; author checksums verified; SHA256SUMS hash 863bb6bf86acb2d51230c8856a2aa34546f2cf9d6afee40fed3d86ddf63c3a8a. Static hypotheses only; no exploit code, attack payloads or live deployment. Author could not run its shell tool but file writing and checksumming completed. This commit precedes every scanner/planner/baseline evaluation. Labels will not change.

T6.2 first raw score: all 25 cases UNKNOWN and all five model-supported cases rejected because required broker/receiver source SHA claim fields were omitted from the author-facing public interface. Scanner correctly fails closed. Record the raw result and then explicitly instantiate the author-given known-code hypothesis in copied model inputs; never alter sealed cases or labels. This is an evaluator-interface correction, not a new runtime observation or automatic scanner pin inference.

T6.2 correction committed before re-scoring: explicit --instantiate-known-code adds actual local trusted-source digests to copied model declarations under the sealed author-given correspondence hypothesis. Raw authored files and labels remain unchanged; raw CLI input still fails closed. This is not baked-image observation. Planner also names each missing/drifted source pin as a residual instead of hiding it behind a generic observation gap. Before score has 50 kernel certificates; corrected score pending.

T6.2 instantiated before-fix score: 50 kernel certificates, zero false model acceptances, 2/5 supported cases rejected (40%), 14/25 UNKNOWN (56%), 22/25 prospective plans accepted and three named residuals. Both supported misses are equivalent receiver mounts listed in a different order in the synthetic inventory. Preserve this result and failing regression. Fix comparison order only for unambiguous unique-target mount lists, keeping every mount field and multiplicity; labels stay frozen.

T6.2 ordering fix committed before re-scoring: selected inventory lists compare independent of order only when mounts have unique targets and string paths; all fields and duplicates survive. Ambiguous targets are not sorted. Networks/environment names retain multiplicities. Known UID and undeclared-writer mismatches remain refutations. Corrected score pending.

Tier 6 local exit: 25 independently sealed static configurations, corrected score and 50 kernel certificates PASS; three static/seal/order tests, seven planner tests, 13 slice tests, nine scanner tests, two remediated archive tests, 520 additions and fixture --check PASS. Full 44+250 differential PASS with zero Python/Lean differences. Self-review deployment/reviews/tier6-self-review.md; no real new workload. Final-head CI pending.

Tier 6 exit: b263d0bbde0366ec84f2b2f3c9acbe23790b05d2, 18 CI SUCCESS and three explicit SKIPPED; #50 remains draft/open. Receipt deployment/runs/tier6/ci-receipt-b263d0b.json. Tier 7 stacks on that exact tip.

ID | status | evidence path or reason
---|---|---
T7.2-original | GATED | New attack policies excluded by John’s defensive-only decision; no cyber-permissive access tier available to the owner
T7.3-original | GATED | Original four-arm attack evaluation requires cyber-permissive access the owner does not have; replace only with archived outcome attribution, never claim four-arm results

T7.1 freeze: new analysis preregistration and all Tier 2/Tier 5 source hashes committed before attribution execution. Exactly nine episodes; six explicit honest workflow completions. Retrospective known outcomes, no randomized arms or new attack policies. The original four-arm attack evaluation remains GATED.

T7.1 CI guard: retain the full original protected-path patterns; permit only an A-status addition of the exact authorized new prereg, with current SHA equal to its earliest Git addition blob and frozen source inputs. Any existing prereg edit/delete and every other protected-path change still fails. No frozen artifact is edited.

Tier 7 local exit: nine archived episodes independently replayed; H1-H4 integrity/coverage thresholds PASS, six explicit honest completions, both bypasses retained, one unauthorized sink file. Fifty archived harness durations; three unmeasured episodes and monitor data remain UNASSESSED/null. Four regression tests and first-addition/source freeze guards PASS. No new live workload. Self-review deployment/reviews/tier7-self-review.md; final-head CI pending.

Tier 7 CI attempt 455feb3: fixture FAIL reproducing Inspect export because shallow checkout treated the current commit as the prereg addition, changing eval.created. Raw failure retained. All deployment CI jobs now fetch full history; the guard rejects a prereg addition at a shallow boundary, and the regression checks this explicitly. Attribution inputs/output bytes remain unchanged. Corrected final-head CI pending.

Tier 7 handover (2026-10-11): Sol's Codex thread hit its usage limit after committing 575aad1 locally. Claude (Opus 5.5) is continuing at John's request with the same handoff and rules. Fresh-checkout attribution tests (4 PASS) are recorded in deployment/runs/tier7/fresh-checkout-attribution-tests.txt; the prereg guard PASSes locally. Pushing the corrected head for final CI.

## Tier 8 (Claude, Opus 5.5, continuing Sol's handoff)

T8.2 DOING: `cstack demo --output DIR [--static-only]` (deployment/demo.py). Stages: 44 fixtures verified in Python and the Lean kernel; read-only plans for the two repaired cases; live remediated containers (honest work only, defensive scope); independent sink-side check; DEMO.md report. Exit 0 all PASS, 1 any FAIL, 2 usage, 3 SKIPPED stage (never a pass). Dev-clone run deployment/runs/tier8/demo-dev-clone PASS in 83 s; own resources removed. Fresh-clone run pending.
T8.4 DOING: deployment/schemas/{bundle,plan,demo}-v0.1.json; deployment/golden/ bundles, reports and plans; tools/test_deployment_release.py 5 PASS (golden equality, schema rejection of ASSURED/unknown status, CLI exit codes).

Tier 8 trusted-path review: no finding violates the claim conclusion; M1-M3 stated in the claim with sink-audit and image-capability evidence; trusted code unchanged; hardening queued T9.1-T9.6 (grindable, not resource-gated).

Tier 9 (Claude Opus 5.5, after Sol's usage limit): T9.1 done. deployment/pins.py keeps every trusted-source generation under deployment/pinned-sources/ (append-only, hash-checked bytes). Archive checkers and replays (collect(replay=True), scan replay, portable IR relabelling) accept vaulted generations; fresh scans still require the current tree. Probe: a one-line edit to controller.py left r2, remediated, attribution, evidence and every archived replay passing; only current-reference goldens/examples moved, as intended. tools/test_deployment_pins.py (6 tests) is in the release workflow.

T9.2 done (generation r2-v1): server.run_one/serve take allow_delegation (library default on for the delegated-model tests); the broker CLI defaults it off behind --allow-delegation, refuses a database with delegation rows, and deployment/scan.py flags an entry that enables it. tools/test_deployment_hardening.py (6 tests). The Landlock confined-effect test cannot run on this host (no Landlock; unchanged).

T9.3 done (generation r2-v2): server.py threads with a total 3 s frame deadline, 2 connections per UID / 12 total, '{'-first frames, catch-all per connection (nested JSON no longer ends the broker), halt_with_retry, unsigned peer UID, admin-euid check before bootstrap, restart reopens the DB (cap must agree) and clears only a dead owned socket. Open: Principals still accepts UID 0 (stated in the review disposition). 8 new tests in tools/test_deployment_hardening.py; real-UID tools/test_trusted_stack_broker.py (sudo) passes.

T9.4 done: extractors/compose HARDENED/declared_hardening; collector v2 inventory (`hardening`, hardening=True; archived v1 replay via inventory_has_hardening); agent UNKNOWN edge when a v2 inventory lacks no-new-privileges/cap_drop ALL; fresh scan refuses v1 inventories and records image file capabilities (PAX xattr). Legacy 44-fixture corpus and archived examples stay byte-identical (archives are bound to them); additive hardened corpus examples/compose-two-agent-hardened + security_ir/fixtures-hardened (5 fixtures, kernel-checked in the demo: 49/49). plan.py now adds both settings to agents; golden plans regenerated, hardened-clean golden bundle added. Live evidence is T9.6.
