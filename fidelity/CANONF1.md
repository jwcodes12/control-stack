# Fidelity audit (orchestrator): CANONF1, a verified canonicaliser

Statement: `ledger/CANON.lean`, frozen as CANONF1 (sha d3d1dd97809f). Informal source: DESIGN.md v1 §3 (CANON).
Proof: 757 lines by an isolated prover agent; gated with standard axioms.

**Definitions checked by me.**
- `Exec` is a standard relational big-step semantics. `cfor` is defined by the C11 §6.8.5.3 equation. Reviewer B noted this
  makes desugaring preservation nearly definitional; that is intended. The restriction (no break/continue/scope) is
  stated in the docstring.
- `Runs` requires `ins.length = nparams`. Parameters `0..k-1` are bound to the inputs; every other variable starts at 0.
  So there is no uninitialised-read issue (Reviewer A #25).
- `canon = rename canonMap ∘ (flatten ∘ desugar)` is executable code: no choice, no `Classical` in its definition. The
  `open Classical in` scopes only `Claim`, for decidability of `SynEquiv` inside `Finset.filter`.
- `SynEquiv = EqvGen Step`. `Step` = one `ForStep` (for→while desugaring or `;`-reassociation, at any statement
  position) or one admissible renaming. Admissible means: fixes parameters, keeps locals local, injective on the
  program's variables. These are exactly the three declared freedoms.

| conjunct | binders and hypotheses | classification | verdict |
|---|---|---|---|
| (i) Runs (canon p) ins out ↔ Runs p ins out | ∀ p ins out | SOURCE; terminating runs only, since relational semantics; divergence is preserved implicitly because neither side has a run | faithful |
| (ii) canon p = canon q ↔ SynEquiv p q | ∀ p q | SOURCE | faithful |
| (iii) class-agreeing laws have equal canonicalised laws | finite X, `prog`, PA, PH; agreement on every ≈-class | SOURCE. Reviewer A: this is a statement about *marginal* laws. With a shared seed ω, the conclusion "every monitor's pass rate is equal" needs class-agreement conditional on ω, or a monitor that sees only canonical output and does not depend on ω. The docstring's sentence is the ω-free reading | faithful as stated; docstring over-reads slightly (recorded) |

**Witness.** A `for` program and a `while` program with different local names are identified and compute 3 on input 3.
A semantically different program is not identified. Non-degenerate.

**Scope (stated in the docstring).** Only the three freedoms are erased. Operand order, statement order, dead code,
constants and the like remain collusion channels, so δ for `canon` equals δ for ≈-classes, which is still very large.

**Novelty.** Standard techniques (canonical forms modulo α-equivalence and desugaring). The value for the stack is a
*verified trusted component*: deterministic code proved correct, as the programme asks for.
