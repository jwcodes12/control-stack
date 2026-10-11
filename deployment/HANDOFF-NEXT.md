# Handoff (2026-10-11, after PR #54): what is left, in the order the owner chose

State: **all PRs merged, none open.** #45-#53, #43, #41 earlier; **#54 (Tier 10) merged as 262e4ec**. Level: scoped R2, every section 7
gate met for the local-file two-agent slice **except independent human review (G1)**. Source generation `r2-v7`. Read `END-STATE.md`, then
`docs/DEPLOYMENT-CLAIM-v0.md` (section "Tier 10"), then `deployment/REVIEW-PACKET-R2.md`.

Owner's order of work: (1) close PRs [done], (2) simplify the Lean, (3) the human/resource-gated work, (4) researcher-friendly presentation
(plan only: `docs/PLAN-RESEARCHER-FRIENDLY.md`). Standing rules: defensive-only scope; never launch dangerous fixtures; frozen paths
(`ControlStack/EgressGate.lean`, `prereg/*`, `ledger/`, `proofs/`, `*/evidence/*`) are not edited; container resources use the `cstack-r2-` prefix and
are cleaned up (only `postgres:16-alpine` should remain); Opus reviews = Opus 5.5 via a Claude Code subagent only; publication, tagging and
outreach are the owner's call.

## 0. In flight: the one-to-one check of the English statements (Sol, proofledger gate)
- 187 headline Lean claims are stated in plain English (`docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md`, blocks in `docs/lean-english/part-g0..g7.md`, written
  by Sonnet from the Lean). Of ~2,222 declarations in the registry only these are translated (~9%); supporting lemmas are not.
- Sol's task: blind back-translation of each English block to Lean, gate-checked equivalence proof. Instructions `/var/tmp/sol-eval/HANDOFF-SOL-ONE-TO-ONE.md`,
  protocol `docs/lean-english/ONE-TO-ONE.md`, results `docs/lean-english/one-to-one/RESULTS.md` (also merged into main as Sol's in-progress output; the
  folder is large and includes transient logs and receipts).
- **G0 (26 deployment claims) finished:** 19 equivalent, 2 weaker, 3 stronger, 2 undecided. 6 planted-wrong canaries were in the input (key is in the
  orchestrator's scratch dir, not the repo): 5 flagged cleanly, 1 (`halted_absorbing`, a stronger-but-true statement) was passed as EQUIVALENT with a note.
  Real findings on the Sonnet English: `Accepted` identity check is "iff", not "only if" (weaker); `runtime_trace` omits the ten-step ordering (undecided).
- Caveat Sol disclosed: the G0 pass was **not strictly blind** (typed Lean encodings were written after comparing with the source). A strict blind
  pass is still owed. **G1-G7 (161 claims) not reached.** Equivalence of two *true* closed theorems is trivial, so verdicts compare conclusions under the same hypotheses.
- Sol also proved the missing provenance invariant (`docs/lean-english/one-to-one/ProvenanceDraft.lean`: ApprovalProvenance preserved by every Step,
  and `deployment_broker_provenance`). It is a draft outside `ControlStack/`; not yet integrated. Until it is, the claim of record ("reviewed, exactly
  approved, once-consumed release") is stronger than `deployment_broker_safe` concludes.

## 1. Next: simplify the Lean (proposal; scope needs the owner's decision)
1. Integrate the provenance invariant into `ControlStack/Deployment/` (new file, add to the contract witnesses with positive and negative examples), then reword the
   headline claim to what is proved.
2. Replace the 21-conjunct `Allowed` and the six-part `Accepted` by structures with named fields, proved equivalent to the current definitions.
3. Dedupe: the per-scenario `AuthInstancesA/B`, `*Refinement` and `*Liveness` files repeat three generic patterns (Gate invariant, authenticated adversary, refinement
   transfer). State each pattern once and make scenario claims instances. Use the registry (2,222 declarations, 2,147 without an adversary class) to find unused and duplicated helpers.
4. Apply the corrections the one-to-one check found to the English blocks; regenerate the overview (`tools/build_lean_english_overview.py`).
5. Decide T4.2: the literal monotonicity is false (3 kernel countermodels); keep only the safety-only theorem and say so everywhere.
6. Check whether the covert-channel and audit lemmas already exist in `~/research/alignment-contrib/lean/StabilityDebate`, `control-tree`, `proofledger`.
Every Lean change: registry and statement catalog regenerate (`tools/build_registry.py`, `tools/build_statement_catalog.py`), `check_deployment_*` kernel checkers pass,
axioms stay standard. Changes to `trusted_stack/*.py` need the recipe in section 4.

## 2. Then: needs a person or a resource (GATED)
| ID | Needs |
|---|---|
| G1 | **Independent human review** of the statements (now with plain English and one-to-one verdicts to start from), scanner semantics, enforcement, evidence. Start with `deployment/REVIEW-PACKET-R2.md`, `deployment/reviews/t10-open-items-review-opus.md`. Everything so far was built and reviewed by models. |
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

## 3. Then: researcher-friendly presentation (`docs/PLAN-RESEARCHER-FRIENDLY.md`)
Pattern pages, glossary, premise view (29 premises), claim cards with one-to-one badges, counterexample gallery, reading paths, runnable demos, review kit, readable Lean. Deferred by decision.

## 4. Engineering still open, no resource needed (small)
Base image outside `/slice` is trusted, not inspected; receiver-side SQLite lock scheduling; per-agent staging quotas (one agent can exhaust the shared 64 MiB);
a separate filesystem for the database is a premise (agents can fill the host disk through their container layer); archives whose host observations predate the `/slice` inventory
replay without that rule; Tier 2-8 live evidence is generation r2-v0 (only Tier 9-10 exercise the fixed code); `publish_effect` is outside the claim; held-out sets are model-authored, and round 2 had one
false CONDITIONAL before any fix (post-fix numbers contaminated); a strict-blind re-run of the English check is owed.
**Trusted-code changes:** edit; `python3 deployment/pins.py snapshot <next>`; `python3 tools/build_deployment_fixtures.py`; `python3 deployment/pins.py vault-templates`; `python3 tools/build_deployment_golden.py`;
tests (`test_deployment_pins/hardening/scanner/release/plan/heldout/slice`); then rebuild the image and re-run `deployment/run_containers.py --hardened`, `cstack demo`, and keep failed attempts as evidence.
The Lean differential test (`tools/test_deployment_lean.py`) takes about 12 minutes; do not time it out at 10.

## 5. Traps
- Do not `git add -A` blindly in the clone: Sol writes into `docs/lean-english/one-to-one/` and `docs/lean-english/sol-input/` (excluded in `.git/info/exclude`; it holds the canary inputs).
- Checkers refuse `python -O`; `Principals` refuses UID 0; the receiver refuses delegated releases unless `allow_delegation`.
- `consolidated-integrity.yml` fetches full history (the shallow fetch broke the prereg guard). SC-01 shared-cache probe in `scenario-a-repair` is a known flake.
- Docker cleanup after any live run: only `postgres:16-alpine` remains. Never launch docker.sock/privileged/host-network fixtures.
