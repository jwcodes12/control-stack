# HISTORY

## 2026-10-08 — structure merge work branch (not yet verified)

- From exact main `18c1859`, selected B's single 28-case `scenarios/` tree and static checker, retained A's two CI roles, and ported C's Lean family scaffold, explicit policy tamper/dual-gate counterexample, adversary taxonomy and future prereg templates.
- Moved six reviewed main theorem implementations without changing their bytes; old Lean module names now import canonical definitions. Generated one source-derived theorem registry (Markdown + JSON; 852 scanned theorem/lemma declarations after the inline-attribute and dotted-name fix) with registry-link checking; did not promote recorded validation to new verification.
- Reconciled SC-27 as a draft attestation scenario; C's dispatch theorem is only a narrower bridge and does not establish independent attestation.
- Known outstanding: no networked shell clone, no elan/lake build or Python full suite run in this environment. See [comparison](reviews/structure-merge/comparison.md) and [remaining steps](STRUCTURE-PLAN.md).
- Every integration commit uses `[skip ci]`; no push to `main`. No frozen prereg/evidence receipt touched. SC-01 assurance manifest source SHA-256 bindings for the two relocated compat facades were explicitly re-pinned; this is metadata, not a regenerated experimental receipt.


- **Session 7 continuation (2026-10-07).** Corrected the VCVio defer game so a missed service check keeps the trusted replacement in place and continues, matching the ledger recursion. The operational game and exact `ENNReal` recursion compile; the calibrated real-valued bridge remains open.
- **Session 7 review (2026-10-07).** Two-family review of the finite-grid transfer draft returned `kill` for classical Bellman stability and `revise` for witness/formulation drift. No restatement or freeze was made; a new version needs a distinct theorem contribution.

- **Session 6 continuation (2026-10-07).** Added an optional-decoder adaptive survival recursion and proved the sharper uniform-seed risk bound. A separate proofport compiled against the existing frozen statement and verified dependencies, with a standard-axiom report; no ledger event or frozen statement changed. Registration and red-team review of a separate strengthening remain.
- **Export refresh (2026-10-07).** Added the checked adaptive sharp-converse modules and updated roadmap status; reviewer identities remain anonymised.

- **Session 6 continuation (2026-10-07).** Added the adaptive balanced-count lemma and weighted finite-path aggregation, including the uniform-seed `t/k` corollary. Connecting the adaptive tester recursion to the path measure remains open.
- **Session 6 continuation (2026-10-07).** Proved the VCVio defer game equals its exact `ENNReal` recursion, and proved the discrete balanced-count power-sum bound used by the sharper adaptive converse. Real-valued defer calibration and the adaptive-transcript application remain open.
- **Session 1 (2026-10-06/07, to ~03:00 UTC).** Reuse decisions and a VCVio spike (REUSE.md); DESIGN v0, hostile
  design reviews before any Lean, DESIGN v1. Verified: UMHSF1, UMSURVF1, UMPROTF1, UMSTRATF1, UMNOGOF1, CANONF1,
  SANDBOXF1; VCVio Spike and HoneypotBridge proved. First final hostile review; STACK.md rescoped.
- **Session 2 (2026-10-07, ~03:00–07:30 UTC).** Verified: SANDBOX2F1, UMLOWERF1, UMUSEF1, UMDEFERF1; VCVio operational
  adequacy (`RefinementProof.lean`). An external critique and a related-work audit narrowed the positioning; a second
  final review; STACK.md revised.
- **Session 3 (2026-10-07, ~12:00–13:30 UTC).** Verified: UMCERTF1, UMADAPTF1; outcome-valued VCVio game
  (`OutcomeProof.lean`).
- **Per ledger result:** exact brute-force numerics first; hostile design review where the statement was new; a red
  team by two foreign model families (Reviewers A and C) on exactly the statement that was then frozen by hash
  (verdicts are bound to the statement hash; the four earliest CIDs had a single proposed version, reviewed before that
  binding was added to the record); a proof by an isolated prover agent; the Lean gate (fixed assembly, banned-token
  scan, standard axioms only: propext, Classical.choice, Quot.sound); an orchestrator fidelity audit (`fidelity/`).
- VCVio-level files are checked with `lake env lean` and `#print axioms`, not by the ledger gate.
- No human expert has reviewed any result yet.
- **This export (2026-10-07):** a single-commit snapshot; reviewer identities anonymised; the sandbox results stated as
  general mount-table lessons; `ledger-check/` added to reproduce the gate.

- **Session 3 update (2026-10-07).** TMCERTF1 and TMGACF1 frozen, independently red-teamed by two reviewer families, and verified by claim and witness gates; export includes statements, proofs, fidelity audits and stack status.
- **Session 5 continuation (2026-10-07).** Added the sampled-ROC design note and exact-rational simultaneous band generator. The realistic checker run remains dependent on labelled validation data. Added a design note for trusted/untrusted monitoring composition; only a common-event minimum bound is currently justified. No theorem was promoted in this update.
- **Session 5 continuation (2026-10-07).** Added an exploratory LASR ROC-band pipeline, a 100-step/two-coin rational interval game, and a kernel-checked TMCERTF1 risk bound. The source sample is not established as deployment-matched or held-out IID. Added a design note on the minimum safe composition claim for trusted and untrusted monitoring.
- **Session 5 continuation (2026-10-07).** Added a VCVio soft-slack honeypot survival bridge: an exact finite uniform rejection coin with hazard `1/ns` yields survival `(1 - h/ns)^n`, with only standard axioms. Full protocol composition remains open.
- **Session 5 continuation (2026-10-07).** Extended the VCVio soft-slack model with seed-conditional whole-protocol factorization and the scalar first-moment inequality `h(1-h/ns)^nh ≤ ns/(nh+1)`. Deployment-bound composition under domination and recall remains open.
- **Session 5 continuation (2026-10-07).** Proved the VCVio soft-slack end-to-end catastrophe bound `(1-r)+r·L·ns/(nh+1)` from row domination and worst-case recall; the other game-level variants remain in progress.
- **Session 5 continuation (2026-10-07).** Added the VCVio soft-slack hockey-stick pass bridge and end-to-end bound `(1-r)+r·(δ+e^η·ns/(nh+1))` under a per-bad-row divergence bound; standard-axiom Lean check passes.
- **Session 6 continuation (2026-10-07).** Added a full-history-dependent rational usefulness checker and soundness bridge. ledger harness claim and witness gates pass with standard axioms; reviewer family red-team passed, but a second foreign-family verdict remains unavailable, so the result is not frozen.
- **Session 6 continuation (2026-10-07).** Added `ControlStack/StratifiedGame.lean`: the operational per-class hard-slack test has the exact product of binomial CDFs, and the seeded protocol factors into seed, stratified survival, and deployment. Lean reports only standard axioms. End-to-end stratified safety and the defer game remain open.
- **Session 6 continuation (2026-10-07).** Completed the stratified VCVio bridge: independent classwise hard-slack tests have the exact binomial product survival law; the seeded protocol factors exactly; under classwise domination, coverage, and worst-case recall, the operational end-to-end bound is `(1-r)+r·L·(sc+1)/(m+1)`. Lean reports only standard axioms. The defer game remains open.
- **Session 6 continuation (2026-10-07).** Added a reproducible `checkUseQ` certificate for the 100-step/three-state/eight-model LASR interval fixture. Both the exact rational checker and full-history selector soundness theorem compile with standard axioms and certify `22873/250 = 91.492`; the sample still lacks established held-out/deployment match.

- **Session 6 continuation (2026-10-07).** Added the exact operational defer recursion and calibrated branch lemmas; the proposed real-valued bridge exposed a mismatch in the exhausted bad-service continuation. The local TMLIPF1 Claim and Witness gates pass, but review remains pending and the campaign is not frozen. The adaptive weighted path bound is proved; connecting the tester recursion remains open.

- **Session 7 (2026-10-07).** Calibrated defer bridge proved (`defer_bridge`); the four VCVio game modules (soft slack, hockey-stick, stratified, defer) are recorded as completed.
- **Session 8 (2026-10-07).** Added `DeferMono.lean`: the monotone audit-then-defer bound (lower bounds on recall, halt hazard and service give an upper bound on catastrophe by `catV`).
- **Session 8 (2026-10-07).** Added `ComposeGame.lean`: trusted + untrusted monitoring in one game, product bound with a tightness witness. The root module now imports every proof file.
- **Session 8 (2026-10-07), continued.** Verified UMADAPTF2 (sharp adaptive converse) and TMCERTUSF1 (usefulness-certificate checker; two review rounds added a non-degenerate witness and an admissible-row check). Both pass `ledger-check`. `UseQ.lean` ported to the stricter checker.
- **Session 8 (2026-10-07), late.** Verified TMLIPF1 v2 (frozen with an approved override; passes `ledger-check`). Added preregistered empirical certifications (LaStraj, LASR held-out test split, LinuxArena 217 with and without environment-split calibration) and a post hoc decomposition of certified risk.
- **Session 8, composition bridge.** `ComposeAvg.lean`: composition with the population-average trusted miss rate, so certified ROC bands plug in.
- **Session 8, review response.** `ComposeBlindSpot.lean` (negative result), post hoc statistical audit, assurance manifests with a no-promotion checker, CI fast tier, roadmap reorganised around one end-to-end safety case.
- **Session 8, P0.** `CATASTROPHE-SPEC.md` (covert secret propagation to machine receivers), `CovertChannel.lean` (bound P ≤ |V|/|M|, tight), fail-closed `gateway/` prototype with adversarial tests in CI.
- **Session 8, gateway.** `GatewayModel.lean` (end-to-end bound for the gateway model), Python/Lean differential test, bubblewrap two-instance harness with side-channel tests.
- **Session 8, gateway v2.** Responded to the covert-channel review (`reviews/dialogue/claude-01.md`): lifetime budget, exact cardinality, frozen config/snapshot, fixed alerts, Lean attainment and lifetime bound, covert manifest, narrow Lean CI.
- **Session 8, replay.** No-go theorems (`CovertNoGo.lean`); offline replay of 9,863 LinuxArena trajectories through a frozen action policy (dev/test by environment): weak separation; host policy catches host-level attacks only.

## 2026-10-08 — Astra/Opus xhigh roadmap consultation

Added independent consultation reports and disposition. Revised priorities around
the bounded exact-secret-recovery contract, measured honest usefulness, lifetime
accounting and complete observation. Monitor-based safety is a separate optional
scenario; egress attribution remains a supporting/separate reachability milestone.
No product code, auditgate source, theorem or assurance assumption status changed.

## 2026-10-08: circle effort (export)

- Adversarial consultation (Astra, Fable): don't build a general certificate calculus.
- Lean, proved with standard axioms only (not ledger-verified):
  - `Leakage`: leakage transfer with stateful side channels and leakage-sensitive adaptive auditing;
  - `LeakWitness`;
  - `Necessity`: witnesses;
  - `Gate` / `GateClients`: shared gate interface, F4 artefact gate, F7 approval;
  - `Lease`: F5.
- The SC-01 checker separates applicability and exits 3 when a hypothesis is refuted.
- `ctrlcert` researcher CLI.
- Adversarial review by Gemini 3.1 Pro and Opus 5.5: findings fixed or documented.
- Pickup notes: `CIRCLE.md`. Plan for work that needs no testing: `STRUCTURE-PLAN.md`.

## 2026-10-08 — independent scenario checker hardening [skip ci]

On a separate `structure-merge-20261008-gpt6-finish` branch derived from the concurrently updated merge head: added a required fourth named-assumption usefulness status and six conservative scope review axes to 28 scenario manifests. SC-01 retains explicit shared-cache and VM usefulness failures; other unknown usefulness is NOT_RUN. Added fail-closed validation for missing/unsupported scope, duplicate JSON keys and lexical source declarations with regression test cases. Consolidated the three B draft preregistration documents into `prereg/` without changing frozen root `PREREG-*.md` or any experimental receipts. No Lean build, scenario experiments or full Python tests were executed in this environment because GitHub DNS resolution and Lean toolchain installation were unavailable. Nothing is deployment assured and no new mathematics is claimed.

## 2026-10-08 — Clean integration CI acceptance [skip ci]

GitHub Actions run [#37870787641](https://github.com/jwcodes12/control-stack/actions/runs/37870787641) **passed** with 3,743-job root Lean build, 28 Lean claim elaborations, 8 standard-only claim axiom reports, registry consistency (860 lexical declarations), 18 scenario mutation tests and 4 certifier tests. SC-01 checker phases 1–4 passed; the frozen prior-host OpenSSL cache-binding mismatch at phase 5 was isolated as expected and no historical receipt was changed. All 25 draft scenarios remain draft; 3 conditional cases are not deployment assured. See `reviews/structure-merge/hardening-validation.md`.

## 2026-10-08 — Pinned independent A/B/C branch replay and halt-liveness acceptance [skip ci]

Exact original A, B and C source SHAs independently passed `lake build ControlStack` (3,715 jobs each), 8/7/7 checker mutation tests, and B's 28 original Lean claim replays. A generated indexes pass. Original C generator drift was confirmed as an unmerged-branch defect; the merged 865-entry registry is current. Successful expanded model CI [#37877045361](https://github.com/jwcodes12/control-stack/actions/runs/37877045361) compiled the new conditional HALT delivery/freezing/necessity theorems with only `propext`/`Quot.sound`, plus full merged suite. No scheduler fairness, runtime attestation or deployment safety is inferred. [Evidence and comparison](reviews/structure-merge/comparison.md).

## 2026-10-08 — Final exact integrated code acceptance PASS [skip ci]

[CI #37877960110](https://github.com/jwcodes12/control-stack/actions/runs/37877960110) passed a fresh full Lean 4.34.0 build of 3,744 jobs and the 28 scenario claim replays, 18 checker tests, 4 certifier tests, registry consistency and unchanged SC-01 checks 1–4. Historical source-bound OpenSSL cache receipt remains an expected non-portable check, never regenerated. Main unmerged pending owner approval.

## 2026-10-08 — SC-01 source-level runtime gate audits, no protocol change [skip ci]

On a separate work branch, added bounded independent reference-gateway differential checks, two mutation-negative AST sender-to-receiver field guards, read-only ARM64/x86 GitHub hosted KVM feasibility probes and a theorem-statement premise matrix. CI #37880911299 passed the Python and KVM-read-only jobs. Frozen 0.25 s, 64-lifetime VM usefulness gate remains FAILED 0/64 in both conditions and the complete-observation premise is UNRESOLVED. No preregistration/evidence receipt or gateway/guest source was changed. No external reviewer or hardware VM test took place.

## 2026-10-08 — Full read-only proof/transition audit validation PASS [skip ci]

[CI #37880911299](https://github.com/jwcodes12/control-stack/actions/runs/37880911299) passed 3,744 Lean jobs and kernel axiom replays for SC-01/13 and conditional HALT, 5 gateway finite model tests, 3 static receiver-field mutation controls and original gateway/ledger/certifier tests. GitHub ARM64 host has no KVM; GitHub x64 KVM API v12 and paused native x64 QMP acceleration check passed in privileged read-only infrastructure tests. A new pinned x64 guest port, an approved operational setup, actual 64-lifetime usefulness success, all-observation correspondence and independent statement review have **not** been completed.

## 2026-10-09 — F1–F8 reference control sprint [skip ci]

Added combined SQLite reference authorization records for F4 content provenance, F5 shared transactional budgets, F7 distinct peer-authenticated approval/nonces, and F1/F3 sticky halt/check-before-record, plus an ideal hidden F6 schedule and F8 joint accounting. Added Linux SO_PEERCRED integration fixture, synthetic invalid/effect tests, and source-normalized Lean review catalog for all 865 indexed declarations. None of this certifies arbitrary OS effects, harmful tool calls, complete leakage observation, no rollback, independent review or 25 draft scenario assurance. See ROADMAP.md for remaining exact acceptance gates and root COMPLETED.md for validated work and CI provenance.
