# Fidelity audit (orchestrator): TMLIPF1, parameter-Lipschitz certificate transfer

Statement: `ledger/TMLIP.lean` v2 (frozen 5c844eb0129e, **with override**). Depends on TMCERTF1. Proof: 204 lines, gated
(claim and witness), standard axioms. Session 8.

History:
- **v1** (session 5): Reviewer A kill (trivial tool: Bellman stability) plus formulation gaps; Reviewer C revise
  (witness/claim drift). Not frozen.
- **v2** (session 8) fixes every listed gap: arbitrary target `Set P`; the conclusion names the grid point q, its
  certificate V, V's range and bound U, then the inflated certificate; explicit `OneStep` Bellman-error lemma; `GridRisk`,
  a policy-quantified risk corollary via TMCERTF1 (Fx); a witness with N = 1 sharpness, failure of the uninflated
  certificate, N = 2 horizon accumulation (7/16 > 1/4) and a real-parameter grid instance satisfying every hypothesis.
  Reviewer A: kill on the trivial-tool criterion ONLY (no vacuity, no wrong reasons, witnesses aligned; one minor note:
  `dist` nonnegativity not required, which does not affect the inequalities). Reviewer C: pass.
- Frozen with `--override`: John approved banking classical-but-verified lemmas as infrastructure (2026-10-07). It is
  needed to transfer certificates under estimation error.

| element | classification | note |
|---|---|---|
| `RowClose`, `InRange`, `Inflated`, `BellmanRow` | SOURCE | as the question specifies |
| `OneStep` | SOURCE | |Δ Bellman row| ≤ row distance for [0, 1] continuations |
| `Transfer` | SOURCE | V + n·ε certifies a lawful row-close H |
| `GridTransfer` | SOURCE | arbitrary target set; coverage, Lipschitz relation and grid certificates are hypotheses |
| `GridRisk` | SOURCE | every Red policy's risk ≤ U + N·L·h on every target model |
| Witness | SOURCE | exact instances; no statistical claim |

Classical (finite-horizon simulation lemma / Bellman stability plus a finite net). Not novel; infrastructure.
