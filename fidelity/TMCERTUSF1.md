# Fidelity audit (orchestrator): TMCERTUSF1, rational usefulness-certificate checker

Statement: `ledger/TMCERT_USEQ.lean` v3 (frozen 3b0cda8ceba9). No dependencies. Proof: 110 lines, gated (claim and
witness), standard axioms. Author family: Reviewer A's; foreign reviews by Reviewer C and the prover agent's
family.

History:
- **v1**: Reviewer C pass. Prover-agent-family review: revise. The Witness was degenerate (N = m = t = 1, K = 0: the
  transition sum, selector, history and admissibility were never exercised). Replaced by an N = m = t = 2 witness
  with stochastic rows and a real selector choice (floor 3 accepted; 4 rejected in a probe). Claim unchanged.
- **v2**: Reviewer C pass. A fresh prover-agent-family review: revise. `checkUseQ` did not check that every
  (step, state) has an admissible row; with no admissible rows it accepted floor 10^6 while soundness held only
  vacuously (checked in Lean). Fix: the checker requires an admissible row at every (i, s); the Claim exports this and
  adds a conjunct that an accepted certificate admits an admissible selector.
- **v3**: Reviewer C pass; prover-agent-family pass. Frozen and gated.

| element | classification | note |
|---|---|---|
| `checkUseQ` | SOURCE | exact rational: t > 0, floor ≤ W[N, s₀], W[0, ·] ≤ 0, an admissible row at every (i, s), Bellman sub-solution on every admissible row |
| reflection conjunct | SOURCE | the accepted Boolean check unfolds to the real inequalities |
| selector existence | SOURCE (v3) | non-vacuity of soundness for every accepted certificate |
| soundness | SOURCE | K ≥ 0 on admissible rows and an admissible history-dependent selector give floor ≤ honestValue |
| Witness | SOURCE | N = m = t = 2, stochastic rows, adversarial row choice; floor 3 is the true worst case |

Notes (non-blocking, from the reviews): the stage index counts steps remaining; rows need not sum to 1, so honestValue
is an expectation only for stochastic rows (the theorem is more general); `wAdm 1 0 1 = false` in the Witness is not
load-bearing; selectors are deterministic history-dependent functions. Classical: the robust-DP comparison principle
(Iyengar 2005; Nilim and El Ghaoui 2005). Banked as infrastructure, not as a novel result.

Game level: `ControlStack/UseQ.lean` now uses the v3 checker and proves the same three conjuncts (session 8). The LASR
fixture `numerics/lasr_usefulness_certificate.lean` re-checks under it (`decide +kernel`, standard axioms), so that
certificate was not vacuous.
