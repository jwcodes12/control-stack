# HISTORY

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
