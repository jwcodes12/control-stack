# HISTORY

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
