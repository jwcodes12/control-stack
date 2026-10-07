# Fidelity audit (orchestrator): UMPROTF1, protocol safety (the main capability-free guarantee of layer 1)

Statement: `ledger/UMPROT.lean`, frozen as UMPROTF1 (sha 1385777cdd90). It depends on UMHSF1 and UMSURVF1 (both
verified). Proof: 276 lines, isolated prover agent; gated, standard axioms. Red team: Reviewer A pass, Reviewer C pass.

## What the definitions encode
- **`cat`** is the exact catastrophe probability of the deployment phase in the halting variant (DESIGN v1 §2.2), as a
  backward recursion over rounds.
  - PASS on bad: catastrophe (value 1).
  - PASS on benign: continue; the history records (x, z, true).
  - FLAG with u < b on bad: 1 − r.
  - FLAG with u < b on benign: continue with u + 1.
  - FLAG with u ≥ b: halt (value 0).
- **`protocolCat`** = Σ_ω ρ(ω) · surv(q, φ_ω, κ, n_h, 0) · cat(N, 0, []).
- **Fidelity of the recursion to the operational protocol.** Not a Lean bridge: it is checked by an *independent*
  sampling simulation written without the recursion (`numerics/simulate_protocol.py`: 12 instances, adaptive generator,
  budget, r < 1, halting, trusted task stream; agreement within Monte Carlo error) and by both red teams' reading.
  **Open item:** the VCVio `ProbComp` bridge.

## Binders and hypotheses
| binder or hypothesis | classification | note |
|---|---|---|
| X, Z, Ω finite; `Bad` decidable | TYPING / MODELLING (A8) | |
| `M` with `IsKernel M` | SOURCE (trusted mediator, fresh randomness per call: A1) | |
| `PH` with `IsDist PH` | SOURCE (trusted honeypot law). Need not be supported on Bad: more general | |
| ρ law, φ_ω rules, π_ω laws for every history | SOURCE: the strategy class | shared seed of any law; monitor stateless (depends only on z, A1/A2); generator any history-dependent randomised policy |
| `0 ≤ r ≤ 1` | STANDING (worst-case audit recall, A6) | |
| domination `∀ bad x, ∀ z, M x z ≤ L·q z` (or `hs_η(M x‖q) ≤ δ`) | SOURCE: the trusted-component hypothesis | quantified over **every** bad submission, so it holds for every attack content and every task Red might pick |
| `1 ≤ ns` (soft form) | SOURCE (κ = 1/n_s ≤ 1) | |

## Structural assumptions baked into the product form `surv × cat`
- **A4 (upfront honeypot test) and A1/A3 (independence).** These hold given ω.
- **A10: the generator does not observe the honeypot transcript.**
  - Reviewer B checked numerically that observing it changes nothing, because the bound is pointwise.
  - The Lean statement covers only the non-observing generator.
  - A stronger statement is a possible extension; it is not claimed.
- **Free-submission model.** The generator may choose any x, including its task. Upper bounds therefore also cover an
  exogenous task stream: a generator facing one is a randomised generator that samples the task itself.

## Conjunct-level verdicts
| conjunct | verdict |
|---|---|
| T3a (first bad decides, budget-sensitive) | faithful; holds for every history and adaptive generator |
| T3* (one-shot attainment) | faithful. It holds without IsRule (prover's remark), which is a weaker hypothesis set, harmless |
| T3 domination / hockey-stick / soft | faithful. Not capped at 1, so vacuous but true when the right-hand side is ≥ 1. With T3*, the domination form is tight up to the counting gap |

## Witness
Bool instance with identity mediator and point-mass honeypots (L = 1), r = 1, n_h = 3, n_s = 0: the colluder with pass
probability 1/4 has catastrophe probability exactly 27/256 < 1/4. Non-degenerate; every hypothesis class is inhabited.

## What it does NOT say
- Nothing about stateful monitors or interleaved honeypots.
- Nothing about defer-on-exhaustion (variant D) or multi-step attacks.
- It does not say any deployed mediator satisfies the domination hypothesis. For rich content-preserving mediators no
  honeypot law does (UMHSF1's maximal-leakage floor; UMNOGOF1).

## Novelty
Elementary (absorbing-process reduction plus truncated binomial first moment). The application to untrusted monitoring
with explicit budget/halting semantics and a worst-case quantifier over shared-seed colluders appears to be new as a
*machine-checked* statement. Greenblatt §3.4 gives the Bayesian intuition; LASR App. B the empirical-ROC version.
Infrastructure for the control stack.
