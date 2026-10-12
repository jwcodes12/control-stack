# Handoff (updated 2026-10-12, after merging main into PR #56): what is left, in the order the owner chose

**Everything here was written and reviewed by models. No independent human review has happened.** Scoped R2, verdict **CONDITIONAL**, not deployment assurance.
Source generation `r2-v7`. Read `END-STATE.md`, then `docs/DEPLOYMENT-CLAIM-v0.md` (section "Tier 10"), then `deployment/REVIEW-PACKET-R2.md`.

## State in one screen
- **Merged:** #41, #43-#55, #57-#61, #63. #55 (Lean simplification and provenance) merged at `0393e96`. #57-#63 are CI speed-ups only (see section 5); they changed no Lean and no assurance gate.
- **Closed unmerged:** #62 (probe).
- **Open: PR #56** (`audit/lean-reuse-187-20261011`). **Do not merge.** `origin/main` (`462c9c7`, #57-#63) was merged into it (`4135804`) and the workflow conflicts resolved (section 0). It no longer conflicts (`mergeable: MERGEABLE`). It is marked **ready for independent human review only**; merging needs that review.
- **CI results by exact head** (read per job, not from the rollup; see section 0 for what each run actually executed):
  - `4135804` (the merge): everything green **except** `deployment-release` / `kernel`, which failed in the full unittest sweep (runner limit, below).
  - `e78e225` (sweep fix): every workflow green, including a real (not marker-skipped) `deployment-release` `full-build` and `kernel`. `consolidated-integrity` / `kernel-review` was satisfied by the green-input marker from `4135804` (same input hash; it ran for real there).
  - `db7b7ca` (first handoff update, docs-only): all 14 workflow runs green, but on attempt 1 the three kernel jobs were satisfied by the green-input marker, which is not a run on that head. The three matching marker caches were deleted and `deployment-release` and `consolidated-integrity` re-run (attempt 2, same head): `full-build` (full `lake build`, both `--check` steps), `kernel` (batch negative controls, ~639 s differential, sweep with the scanner module reported SKIPPED, held-out corpora, demo) and `kernel-review` (`lake build`, both `--check`, F6/F8 kernel check) all executed and succeeded **on `db7b7ca`**.
  - The commit that added this triage is again docs-only (`deployment/HANDOFF-NEXT.md` is outside every kernel input hash), so its kernel jobs were re-run the same way (markers deleted, workflows re-run); read `gh run list --branch audit/lean-reuse-187-20261011` and the PR description for the final head. A marker-skipped job or a green run on an earlier commit is not a receipt for a later head.
- **Open issues:** #7 (reference broker: runtime refinement and remaining deployment gates), #2 (SC-01 usefulness and lifetime accounting), #1 (SC-03 egress negative controls).

Owner's order of work: (1) close PRs, (2) simplify the Lean, (3) the human/resource-gated work, (4) researcher-friendly presentation (plan only: `docs/PLAN-RESEARCHER-FRIENDLY.md`).
Steps 1 and most of 2 are done; what remains of 2 is in section 1. Standing rules: defensive-only scope; never launch dangerous fixtures; frozen paths
(`ControlStack/EgressGate.lean`, `prereg/*`, `ledger/`, `proofs/`, `*/evidence/*`, `deployment/runs/*`, the SHA-pinned scenario Lean files, `trusted_stack/*.py`, the source-pin vault)
are not edited outside the recipe in section 4; container resources use the `cstack-r2-` prefix and are cleaned up (only `postgres:16-alpine` should remain);
Opus reviews = Opus 5.5 via a Claude Code subagent only; publication, tagging and outreach are the owner's call. Do not dispatch Sol or another agent for the gated work unless the owner says so.

## 0. PR #56: done (2026-10-12), pending independent human review
What was done:
1. Merged `origin/main` (`4135804`). Conflicts were only in `consolidated-integrity.yml` and `deployment-release.yml`. Kept #57-#63's runner selection (`vars.CI_RUNNER`), green-input-hash skip markers, the `full-build`/`kernel` split and the per-job demo directory. Kept #56's `build_lean_dependencies.py --check` and `build_lean_traceability.py --check` (in `deployment-release` `full-build` and in `consolidated-integrity` `kernel-review`, both after a full `lake build`), the index artifact upload, the batch-fixture negative controls, the `GuardNecessity`/`ComposedAssurance`/`SC16RefinementReuse` builds in `kernel`, and the full `tools.test_deployment_*` and `trusted_stack` sweep. Dropped the temporary `push: [audit/lean-reuse-187-20261011]` triggers (they existed only because the conflicting PR could not run `pull_request` workflows). Added `docs/lean-english/*.md` to the two input hashes, since the `--check` steps compare against the committed Markdown too.
2. CI on `4135804` failed in `deployment-release` / `kernel`, sweep step: `tools/test_deployment_scanner.py` runs `sudo -n chown` in `setUp` and the self-hosted runner has no sudo (16 errors; the loop aborted there, so `test_deployment_slice` and the `trusted_stack` discovery did not run). Not a code defect: the same module passes on the hosted `deployment-slice` `fixtures` job. Fix (`e78e225`): the sweep prints `SKIPPED ... NOT verified by this job`, a warning annotation and a step-summary line for sudo-requiring modules when `sudo -n true` fails, and continues. **That module is therefore verified only by `deployment-slice` `fixtures` on a hosted runner, not by `deployment-release` `kernel`.**
3. Results on `e78e225` (all jobs read individually; the same three kernel jobs were then re-executed without markers on `db7b7ca`, see the state block): `deployment-release` `fixtures`, `full-build` (full `lake build`, both `--check` steps, index artifact upload) and `kernel` (subset build, batch negative controls, the ~11-minute Python/Lean differential, full sweep, contract witnesses, transcript replay, held-out corpora, demo) succeeded; `live-containers` skipped (always skipped on GitHub runners; not a pass). `consolidated-integrity` `source-fidelity` succeeded; `kernel-review` was marker-skipped (identical inputs to `4135804`, where it ran for real: `lake build` plus both `--check` steps, exit 0). `deployment-slice`, `fast-checks`, `fast-lean` (feedback only), `egress-boundary`, `broker-joint-model`, `scenario-a-repair`, `checked-trace-kernel`, `f6-f8-concrete-review`, `generated-assurance-indexes`, `scenario-metadata`, `statement-catalog-drift`, `trusted-filesystem-outbox`, `fidelity-audit-reproductions` succeeded; `linux-boundary` skipped.
4. Skips inside green jobs (not passes): `tools/test_deployment_scanner.py` (no sudo; see above); 2 tests skipped in `tools.test_deployment_runtime` and 2 in the `trusted_stack` discovery (most likely the `NO KERNEL EVIDENCE` / `NO AGENT EVIDENCE` Landlock and non-root cases in `trusted_stack/test_agent_confinement.py`, i.e. G5; the runtime module's skip reasons are not printed in the log and were not investigated).
5. No Lean declaration changed, so the two committed indexes (187 rows each, generated by Actions run 38305198847) were not regenerated and still pass `--check` at this head. If a later change alters declarations, regenerate **on the pinned runner** and commit the exact bytes.
6. The PR description lists everything still unverified; the PR is marked ready for independent human review only. **Never merge it without that review.**
What #56 added: `GuardNecessity` (five single-deletion countermodels for `TrustedBroker.Allowed`; the other 16 broker guards are **not** proved minimal), `ComposedAssurance` (joint sink-writer exclusivity, capped unique nonces and provenance, with a satisfiable witness; publication sublist, extraction faithfulness and runtime correspondence stay assumptions),
the SC-16 refinement bridge, the corrected `runtime_trace` English, the 187-claim dependency and traceability indexes, the batch-fixture report-identity checks, and design-only notes (`RELEASE-LOG-DESIGN.md`).
Still unverified after this work (full list in the PR description): no local Lean (everything Lean-side is CI-only); strictly blind one-to-one checks (G0 rows 1, 2, 3, 5, 12, 16, 20, 23 stale; G1-G7 never checked); no live Docker/sudo/offline-rootfs run; no independent human review; the sudo-needing scanner module and Landlock tests are not covered by the kernel job.

## 1. Lean simplification: what is done, what remains
Done in #55 (details in `docs/lean-english/SIMPLIFICATION-NOTES.md`, `REUSE-AUDIT.md`):
- Provenance invariant integrated as `ControlStack/Deployment/Provenance.lean` with positive and negative witnesses. It holds only under the assumed `BrokerProtocolRefinement`. **No historical exact-byte or destination release theorem is claimed.** `deployment_broker_safe` is unchanged (used approval); the provenance theorem is supplementary.
- Named-field views and `↔` proofs for the 21 `Allowed`, seven `BaseAccepted` and six `WritersChecked` conditions. The existing predicates and runtime checks were not replaced.
- Generic forward-simulation transfer (`Core/RefinementTransfer.lean`); SC-25 uses it through a bridge file (the pinned `SC25Refinement.lean` is untouched). SC-16 got the same in #56.
- T4.2 decided: literal `Accepted` monotonicity is false (three kernel countermodels kept); only the narrow safety theorem `accepted_path_safety_monotone` stays. Say so everywhere.
- Reuse audit of all 187 headline claims: 17 direct core, 75 existing lemma, 70 candidate, 21 unique, 4 repeated rows.
Still open (reviewed 2026-10-12; **no Lean was changed in this pass**, and the indexes are unchanged):
1. The 70 CANDIDATE rows: still none has a precise statement and proof. all 70 are in Lean files whose SHA-256 is pinned in a `scenarios/*/manifest.json` (checked mechanically this pass; `EgressGate.lean` is frozen as well), so replacing them in place would break the pins; the only safe route is a bridge file like `SC25RefinementReuse`/`SC16RefinementReuse`, and each bridge needs the per-scenario invariant/legal-trace side-condition theorem that `REUSE-AUDIT.md` says is missing. SC-07/18/26/27/28 refinements need those side conditions, and liveness files differ in fairness. With no local Lean, an unverified bridge would cost a CI round per attempt for no gain in assurance, so none was attempted. Do not force them to match.
2. Leads in `~/research/alignment-contrib/lean/StabilityDebate`, `~/research/control-tree`, `~/research/proofledger` were skimmed this time. They are audit-budget/safety-game results over Mathlib reals and probability (ROC schedules, saddle points, honeypot untrusted monitoring), a different formal framework from the gate/trace models behind the 187 headline claims. No covert-channel or gate-trace lemma was found there that restates or supports any of the 187 claims; nothing was imported. (A skim only, not a proof of absence.)
3. Release-time provenance (exact digest/destination per release) still needs an owner decision between a separate event log (recommended), a `State` extension, or external signed receipts. Not implemented.
Every Lean change: registry and statement catalog regenerate (`tools/build_registry.py`, `tools/build_statement_catalog.py`), `check_deployment_*` kernel checkers pass, axioms stay standard (no `sorry`, no `native_decide`).

## 2. The one-to-one check of the English statements (Sol, proofledger gate)
- 187 headline claims are stated in plain English (`docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md`, blocks `docs/lean-english/part-g0..g7.md`, written by Sonnet from the Lean). That is about 9% of the ~2,235 registry declarations; supporting lemmas are not translated.
- **G0 (26 deployment claims) was run once:** 19 equivalent, 2 weaker, 3 stronger, 2 undecided; 5 of 6 planted-wrong canaries flagged, `halted_absorbing` (stronger but true) passed as EQUIVALENT with a note. Results: `docs/lean-english/one-to-one/RESULTS.md`; protocol `docs/lean-english/ONE-TO-ONE.md`.
- **That pass was not strictly blind** (typed Lean was written after reading the source). Treat the verdicts as findings on the English, not as verification.
- The findings were applied to the English (`Accepted` identity is "iff", `exclusive_sink`, `database_custody` "or broker", `agent_not_receiver_uid` agents only, `accepted_no_avoided_path` sink/database only, `deployment_broker_safe` "at most the cap", `halted_absorbing`, `runtime_trace` ordering).
  Those eight blocks are now **STALE** in the results table (G0 rows 1, 2, 3, 5, 12, 16, 20, 23) and need a fresh pass.
- **G1-G7 (161 claims) have never been checked.** Sol treats bus messages as information, so more work from Sol has to be given by the owner directly in its Codex thread.
- Resume order (from `docs/lean-english/SOL-HANDOFF.md`): reuse audit (done) -> Lean changes (mostly done) -> **strictly blind** re-run on the deduplicated set (write and hash the typed back-translation before opening the original theorem; flagged claims first; refresh canaries) -> badges only from gate-passing blind results.
  Two true closed theorems are trivially equivalent, so compare conclusions under the same hypotheses. No badges yet; none on the new `Provenance`, `NamedContracts`, `RefinementTransfer` or `ComposedAssurance` statements.
- The claim of record ("reviewed, exactly approved, once-consumed release") is stronger than what `deployment_broker_safe` concludes; the docs now say which theorem proves what.

## 3. Needs a person or a resource (GATED)
| ID | Needs |
|---|---|
| G1 | **Independent human review** of the statements (start from plain English and the one-to-one findings), scanner semantics, enforcement, evidence. Start with `deployment/REVIEW-PACKET-R2.md`, `deployment/reviews/t10-open-items-review-opus.md`. This also gates PR #56. |
| G2 | ControlArena / inspect_ai with real LLM agents (installs, API budget, approval); attack arms need a cyber-permissive tier you do not have. No LLM agent has ever run against the system. |
| G3 | OPA/Conftest, trivy, hadolint baselines (installs). Held-out baselines so far are a hand-written Python rule set (caught 2/20 and 0/26 negatives). |
| G4 | Kubernetes extractor on a real cluster. |
| G5 | Host Landlock (kernel boot parameter). `tools/test_confined_effect_broker.py` and `run_deployment_boundary.py` have never run here; CI `linux-boundary` is skipped. |
| G6 | TPM/HSM key custody, GPU residue, multi-host. |
| G7 | HTTP sink with a real external destination (egress approval). |
| G8 | Windows, macOS, WASI backends (one tested host: OL 9.8 aarch64, Docker 29.8). |
| G9 | Tag, publish, outreach (owner). |
| T7.2/T7.3 | New attack policies and the four-arm evaluation (cyber-permissive tier). |
Also human-flavoured: an independent author for held-out sets (both rounds were models); F6/F8 candidate gates from #41 (monitor recall calibration, live OS correspondence, native-VM usefulness, outside expert review).
Live Docker, sudo and offline-rootfs stages never run on GitHub-hosted runners; a SKIPPED result there is not a pass. The self-hosted runner has no sudo or docker either.

## 4. Engineering still open, no resource needed (small)
Base image outside `/slice` is trusted, not inspected; receiver-side SQLite lock scheduling; per-agent staging quotas (one agent can exhaust the shared 64 MiB);
a separate filesystem for the database is a premise (agents can fill the host disk through their container layer); archives whose host observations predate the `/slice` inventory
replay without that rule; Tier 2-8 live evidence is generation r2-v0 (only Tier 9-10 exercise the fixed code); `publish_effect` is outside the claim; held-out sets are model-authored, and round 2 had one
false CONDITIONAL before any fix (post-fix numbers contaminated); the other 16 broker guards have no necessity argument.

**Triage, 2026-10-12 (no change made for any of these; reasons are the rules, not effort).** Every item is already recorded as a stated limit in `docs/DEPLOYMENT-CLAIM-v0.md` (checked this pass); none was newly discovered.
| Item | Why nothing was done |
|---|---|
| Base image outside `/slice` trusted, not inspected | Inspecting it means extending `deployment/scan.py` and a live image export, then the trusted-code recipe below including a live re-run. Not allowed here. |
| Receiver-side SQLite lock scheduling; per-agent staging quotas | Code is in `trusted_stack/*.py` (frozen); the only edit path is the recipe below, ending in an image rebuild and live `run_containers --hardened`. Not allowed here. |
| Separate filesystem for the database | A deployment premise, documented (`DEPLOYMENT-CLAIM-v0.md`, HALT availability); not a code change. |
| Archives predating the `/slice` inventory replay without that rule | Replay rule set is chosen by recorded keys (`deployment/scan.py` ~l.171); changing it alters replay of frozen archived evidence. Left; documented. |
| Tier 2-8 live evidence is generation `r2-v0` | Needs live container re-runs on the supported host (gated; privileged). |
| `publish_effect` outside the claim | Deliberate and pinned by a test; bringing it under the claim needs its own model, scanner and review. |
| Held-out sets model-authored; round 2 had one false CONDITIONAL | Needs an independent human author (gated). |
| The other 16 broker guards have no necessity argument | No precise statement and proof exists; `GUARD-NECESSITY.md` shows no countermodel to `Safe`/`Coherent`/halt, and their value is provenance/authorization that those invariants do not express. A necessity result would need a new, owner-reviewed provenance-relative statement and a CI round per Lean attempt (no local Lean). Not attempted. |

**Trusted-code changes:** edit; `python3 deployment/pins.py snapshot <next>`; `python3 tools/build_deployment_fixtures.py`; `python3 deployment/pins.py vault-templates`; `python3 tools/build_deployment_golden.py`;
tests (`test_deployment_pins/hardening/scanner/release/plan/heldout/slice`); then rebuild the image and re-run `deployment/run_containers.py --hardened`, `cstack demo`, and keep failed attempts as evidence.
The Lean differential test (`tools/test_deployment_lean.py`) takes about 11-12 minutes (about 640 s on the self-hosted runner); do not time it out at 10. The kernel job runs it twice (standalone step and in the sweep).

## 5. CI as it is now (from #57-#63)
- 20 Lean and heavy jobs in 19 workflows run on the owner's self-hosted runners (`oci-fast-1`, `-2`, user `ghrunner`) by default. Fall back to hosted with `gh variable set CI_RUNNER --repo jwcodes12/control-stack --body '"ubuntu-24.04"'`; return with `gh variable delete CI_RUNNER --repo jwcodes12/control-stack`. Setup and trust notes: `ci/self-hosted/README.md`.
- Hosted jobs skip when a git-blob-keyed marker shows identical inputs already passed on a clean runner (#59, #63). `fast-lean.yml` is feedback only and prints `SKIPPED ... NOT re-verified` for unchanged inputs; the hosted workflows are the authoritative gate.
- The self-hosted runner executes PR code, so it must hold no secrets. If its cache is suspect, delete `/var/lib/ghrunner/lake-build-cache-*`.
- `deployment-release` demo step uses a per-job directory because the runner's `/tmp` persists (#61).
- The self-hosted runner has no passwordless sudo, so `tools/test_deployment_scanner.py` is reported SKIPPED in the `deployment-release` sweep (see section 0) and verified only by `deployment-slice` `fixtures` on a hosted runner.
- Latest `main` also changed the one-command checker (SC-01 Lean compiled in parallel; unlisted project imports compiled so a clean checkout passes, `462c9c7`).

## 6. Researcher-friendly presentation (`docs/PLAN-RESEARCHER-FRIENDLY.md`)
Pattern pages, glossary, premise view (29 premises), claim cards with one-to-one badges, counterexample gallery, reading paths, runnable demos, review kit, readable Lean. Deferred by decision; do not start.

## 7. Traps
- Do not `git add -A` blindly in the clone: Sol writes into `docs/lean-english/one-to-one/` and `docs/lean-english/sol-input/` (excluded in `.git/info/exclude`; it holds the canary inputs, and the key is in the orchestrator's scratch dir, not the repo). `sol-input/` is never committed.
- Never represent a green run on an earlier commit as a receipt for a later head. Hosted runs that only ran on `71593ff` did not cover the later commits.
- Checkers refuse `python -O`; `Principals` refuses UID 0; the receiver refuses delegated releases unless `allow_delegation`.
- Run test modules as `python3 -m tools.test_deployment_*`, not by path (`ModuleNotFoundError: tools`).
- `consolidated-integrity.yml` fetches full history (the shallow fetch broke the prereg guard). SC-01 shared-cache probe in `scenario-a-repair` is a known flake.
- Docker cleanup after any live run: only `postgres:16-alpine` remains. Never launch docker.sock/privileged/host-network fixtures.
