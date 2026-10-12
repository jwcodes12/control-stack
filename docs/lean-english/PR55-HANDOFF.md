# PR #55 continuation — handoff for draft PR #56

**Model-written, model-reviewed work; no independent human review.**
Repository: jwcodes12/control-stack, branch audit/lean-reuse-187-20261011.
PR #55 was unexpectedly merged at source head 0393e96; PR #56 continues the same branch as a **draft** and MUST NOT be merged while obligations below remain.

## Work by original numbered request

| Item | Status | Reproduction / outstanding condition |
|---|---|---|
| 1. Guard necessity | **PARTIAL** | GuardNecessity.lean adds five single-deletion broker countermodels (halt, positive cost, local and joint budget, nonce) and proves property-relative dependence for the 7 BaseAccepted/6 WritersChecked fields. Other 16 broker guards are **not proved minimal**; their security relevance beyond Safe is unresolved. GUARD-NECESSITY.md states the gap. |
| 2. Cross-component composition | **IMPLEMENTED, conditional** | ComposedAssurance.accepted_joint_claim plus an all-hypotheses model witness. COMPOSED-ASSURANCE.md states SC-26/TrustedBroker role and publication incompatibilities. No runtime correspondence is inferred. |
| 3. Refinement reuse | **PARTIAL by design** | SC-25 bridge preexisted, SC-16 bridge added. SC-07/18/26/27/28 require invariant/legal/trace side conditions absent from unconditional generic induction. Pinned originals remain untouched; details in REUSE-AUDIT.md. |
| 4. Environment dependency tracking | **IN PROGRESS, UNVERIFIED** | tools/build_lean_dependencies.py added as bootstrap. Required DEPENDENCIES.json/.md are not yet committed on this handoff snapshot; no passing 187-claim environment or standard-axiom receipt yet. |
| 5. Traceability | **IN PROGRESS, UNVERIFIED** | tools/build_lean_traceability.py added; must consume actual DEPENDENCIES.json. TRACEABILITY.json/.md and consolidated-integrity --check not yet present/verified. Never promote a historical G0 non-blind verdict. |
| 6. English correction | **DONE at source level, NOT revalidated** | part-g0.md runtime_trace no longer asserts ten-step length in theorem statement; docs overview regenerated. Historical verdicts for G0 **1,2,3,5,12,16,20,23 are STALE** after English corrections. G1–G7 (161 claims) never one-to-one checked. |
| 7. Correctness audit | **SOURCE-LEVEL AUDIT** | CORRECTNESS-AUDIT.md has 26 G0 rows and PR theorem groups covering witnesses, restatement/substance, missing exact axiom reports and nonclaims. Not independent proof certification. |
| 8. CI batching | **CHANGED; live negative-control result pending** | Exact per-certificate report names are now checked. test_deployment_fixture_batch_negative.py includes false Lean Accepted certificate, nonstandard axiom and substituted report. It must run in pinned deployment-release kernel CI before receipt. Caching/cancellation reviewed in CI-CHECK-REVIEW.md. |
| 9. Conservative cleanup | **NO DELETIONS** | No unpinned duplicate shown unused with green checker receipts; leave them to avoid damaging imports/registries. |
| 10. Release-time provenance | **DESIGN ONLY** | RELEASE-LOG-DESIGN.md compares separate event-log/refinement (recommended), invasive State extension and external signed receipts. Owner decision required; no implementation. |
| 11. Handoff/roadmap | **THIS DOCUMENT** | ROADMAP.md and deployment/HANDOFF-NEXT.md updated with post-#55 draft status, outstanding work and human-review restriction. |
| 12. Final release gate | **NOT DONE** | No full local sweep on this session; host-only Docker/sudo/offline rootfs unavailable. The latest fully green Actions receipt observed was commit 71593ff; subsequent commits have not yet obtained a complete green **exact-head** result. PR remains draft, unmerged. |

## Critical safety/verification distinctions

1. Safe, Coherent, NamedContracts and guard deletion countermodels are **abstract Lean model statements**, not proof that the real SQLite gateway enforces the modeled guard under OS faults.
2. The final-state provenance theorem does **not** record immutable per-release file bytes or destination. BrokerProtocolRefinement assumes the publication sublist and ExtractionFaithful assumes actual authority capture.
3. The original SC-26 deployment_safe concerns list-based Roles and equality of bank publications, whereas broker-based assurance uses predicate Roles and a potentially lagged nonce sublist. No cross-model isomorphism established.
4. Only five of the 21 broker Allowed guard deletions were demonstrated to break the specified invariants. Missing a countermodel is **not** proof of redundancy for security.
5. Do not change scenario-manifest SHA-256-pinned Lean files, ControlStack/EgressGate.lean, prereg, ledger, proofs, */evidence/*, deployment/runs/*, trusted_stack/*.py, tools/deployment_container_entry.py, or source-pin vault without the required owner-approved pin/live-test process.
6. No sorry, native_decide or nonstandard axioms. Source-only registry/catalog is **not** itself kernel certification.

## Reproduction after the final planned commit

Run on a host with pinned Lean and all required inputs:

```sh
lake exe cache get
lake build
python3 tools/check_scenarios.py
python3 tools/build_registry.py --check
python3 tools/build_statement_catalog.py --check
python3 tools/build_lean_english_overview.py --check
python3 tools/build_lean_dependencies.py --check
python3 tools/build_lean_traceability.py --check
python3 tools/check_deployment_prereg.py --base origin/main
python3 -m tools.test_deployment_fixture_batch_negative
python3 tools/check_deployment_contract_witnesses.py
python3 tools/check_deployment_transcript.py
python3 tools/check_deployment_monotonicity.py
python3 tools/check_deployment_subset_differential.py
python3 tools/test_deployment_*.py
python3 -m unittest discover -s trusted_stack -p 'test_*.py'
```

The two new --check targets cannot pass until the Lean environment outputs and traceability artifacts actually exist. The differential has historically taken about twelve minutes; **no fresh run is claimed**. Do not count GitHub-hosted live-container SKIPPED as PASS.

## Remaining owner decision / release conditions

Complete tasks 4 and 5 from real Lean environment outputs, resolve any strict gate failures, inspect all applicable CI checks on the exact final SHA, execute the full local sweep, and update PR description with every unverified point. Mark ready for review **only after** those software gates are met. **Do not merge** without independent human review. Defer the human/resource-gated G1–G9 and researcher-friendly presentation; do not dispatch Sol or another agent.

**All new and previously existing work discussed here is model-written and model-reviewed, with no independent human review.**


## Continuation on 2026-10-12 — generated indexes remain blocked on Actions

**MODEL-WRITTEN AND MODEL-REVIEWED. NO INDEPENDENT HUMAN REVIEW. DRAFT; DO NOT MERGE.**

The branch now contains the Actions bootstrap emitter for both dependency and traceability indexes, a fail-closed validator for incomplete project closures/nonstandard axioms, negative parser controls, and requirements for CI to recompute both committed indexes against the elaborated Lean environment. The pinned deployment-release kernel job also schedules the complete `tools/test_deployment_*.py` and `trusted_stack/test_*.py` test sweep. **None of these new gates has a final-head PASS receipt.** Some host-only tests may explicitly SKIP; SKIP is not PASS.

The GitHub Actions runs API last showed `71593ff` as the newest completed workflow set for this branch. Later GitHub-connector commits, including the continuation changes, did **not** produce new Actions runs. A temporary close/reopen of PR #56 also failed to create a run. PR #56 was restored to **open, draft, unmerged**. Do not infer a green receipt from the earlier commit.

### Reproduction / bootstrap in approved GitHub Actions

1. In GitHub Actions, manually dispatch `deployment-release` for branch `audit/lean-reuse-187-20261011` (the workflow has `workflow_dispatch`). Check that the run's `head_sha` exactly matches the intended source SHA and inspect the kernel job; failures in Lean compilation or earlier stages must be fixed before treating any output as complete.
2. Download the **complete kernel job log** and run `python3 tools/import_lean_index_bootstrap.py /path/to/kernel-job.log`. This accepts only contiguous `CSDEPCHUNK` and `CSTRACECHUNK` messages, matching 187-row identities, permitted axiom footprints and no verified English claims. The importer is only transport; it does not certify proofs.
3. Commit `docs/lean-english/{DEPENDENCIES,TRACEABILITY}.{json,md}` to this branch. Remove the temporary bootstrap log emitters and leave `--check` mandatory.
4. Manually run `consolidated-integrity` and `deployment-release` at the **resulting exact commit** (plus any other required branch checks). Confirm Lean index regeneration matches checked-in bytes and review every negative-control, kernel and Python result. Green workflows on earlier commits do not satisfy this gate.
5. Only after all software gates are genuinely green may PR #56 be marked ready for **independent human review**. It must remain **unmerged** until that review. Live Docker/offline-rootfs execution and English-to-Lean strictly blind checks remain separate unclosed obligations.

No exact release-byte/destination proof, trusted Python/SQLite/OS implementation refinement, human review, or deployment assurance is asserted.
