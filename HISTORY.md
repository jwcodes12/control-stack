# HISTORY

- **Session 6 continuation (2026-10-07).** Added the VCVio audit-then-defer game, matching `catV` recursion, and a proved one-step probability expansion. The real-valued refinement equality remains open; no theorem is claimed.
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
- **Session 6 continuation (2026-10-07).** Added a full-history-dependent rational usefulness checker and soundness bridge. Proofledger claim and witness gates pass with standard axioms; Google red-team passed, but a second foreign-family verdict remains unavailable, so the result is not frozen.
- **Session 6 continuation (2026-10-07).** Added `ControlStack/StratifiedGame.lean`: the operational per-class hard-slack test has the exact product of binomial CDFs, and the seeded protocol factors into seed, stratified survival, and deployment. Lean reports only standard axioms. End-to-end stratified safety and the defer game remain open.
- **Session 6 continuation (2026-10-07).** Completed the stratified VCVio bridge: independent classwise hard-slack tests have the exact binomial product survival law; the seeded protocol factors exactly; under classwise domination, coverage, and worst-case recall, the operational end-to-end bound is `(1-r)+r·L·(sc+1)/(m+1)`. Lean reports only standard axioms. The defer game remains open.
- **Session 6 continuation (2026-10-07).** Added a reproducible `checkUseQ` certificate for the 100-step/three-state/eight-model LASR interval fixture. Both the exact rational checker and full-history selector soundness theorem compile with standard axioms and certify `22873/250 = 91.492`; the sample still lacks established held-out/deployment match.
