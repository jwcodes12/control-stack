# Fidelity audit (orchestrator): TMCERTF1, a certificate checker for finite-horizon stateful control games

Statement: `ledger/TMCERT.lean` v2 (frozen 53a3bc12f43c). No dependencies. Proof: 448 lines (isolated prover agent),
gated, standard axioms. Session 3, direction (A) (trusted-monitoring layer).

History:
- **v0** (single statement with the GAC instance): MAJOR from both design reviewers (no false conjunct).
  - The certificate was not finite or checkable (unbounded horizon, unrestricted Θ).
  - The nature selector (rectangular) was conflated with fixed-model uncertainty.
  - "Every observation-restricted Red" needed an explicit interface.
  - T2 "loses nothing" was true only for the full-information Red.
  - T3 usefulness was detached from the controller.
  - There was no bridge from the GAC game to GAC's recurrences.
  - The separation toy was degenerate (unmonitored after exhaustion).
- **v1**: split into TMCERT (core) and TMGAC (instance). Reviewer A: minor. Reviewer B: major.
  - Plain `decide` cannot evaluate the ℚ checker (core rational arithmetic is irreducible); `decide +kernel` can.
  - Vertex checks, the checker and the abstraction theorem did not compose: equality coverage was too strict, and
    componentwise domination is false without V ≥ 0.
  - Selector admissibility was demanded beyond the horizon.
- **v2**: horizon-bounded selectors and nonnegativity; probability range (P); fixed-model corollary for one model;
  checker with guards t, k > 0, V ≥ 0 at all indices, and lawfulness at all horizons; wired hull lemma; value-domination
  coverage `CoveredV` (equality is a corollary); docstring on what a lab must establish.

| element | classification | note |
|---|---|---|
| `Game`, `risk` with nature `θ n h s a` | MODELLING | Blue's controller folded into rows; Red sees the full abstract history; nature picks rows per cell (rectangular) |
| (S), (S'), (P) | SOURCE | the finite-horizon supersolution verification theorem; algebraic bound, a probability when rows are lawful |
| (Fx), (FxGap) | SOURCE | fixed-model corollary; rectangular strictly more conservative (3/4 vs 1/2) |
| (Obs) | SOURCE (interface) | observation-restricted Reds are lifted policies; extra information must enter through (Abs) |
| (T), (TR) | SOURCE | Vstar/Vrob least certificates, attained by deterministic time-dependent Markov Red (and nature) |
| (U) | SOURCE | usefulness sub-solution for the SAME controller (honest action a₀) |
| (Q) | SOURCE | a computable rational checker with a proved soundness bridge; instances by `decide +kernel`; checks every row of every listed model |
| (Vx) | SOURCE | vertex certificates certify the convex-hull family |
| (AbsV), (AbsEq) | SOURCE, scoped | deployment through an abstraction: conditional on universal row coverage of a concrete game that carries every row-moving piece of information; an average ROC does not discharge coverage |

**Reading.** A finite table of rational numbers, checked by the Lean kernel, bounds the catastrophe probability of every
randomised history-dependent Red against every admissible per-cell choice of model, and the bound is exact for the
full-information Red. What the theorem does not supply is the coverage hypothesis: that the deployed system's rows lie
in the admissible set. Capability re-enters there.

**Novelty.** Classical infrastructure (MDP verification theorem; Bellman; robust DP with rectangular uncertainty, Iyengar
2005; simulation by abstraction). The value is the checked certificate format with a proved checker and explicit
uncertainty and abstraction interfaces.
