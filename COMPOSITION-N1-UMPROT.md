# Design note: composing trusted and untrusted monitoring

**Status (session 8):** a product composition is proved for one concrete joint protocol, `ControlStack/ComposeGame.lean` (standard axioms; game-level, not ledger-gated). See "Proved instance" below. The general marginal-bounds discussion stands.

## Proved instance (session 8)

Joint protocol: the untrusted monitor is honeypot-tested exactly as in UMPROTF1. In deployment each submission `x` also goes to a trusted monitor `T x` with **fresh coins** (it does not see the colluders' seed and is not chosen by Red). A submission passes only if both monitors pass it. A flag from either sends it to audit while budget lasts, then halts. Generator and audit see the full history, including the trusted verdicts. Trusted false positives on benign work consume audit budget.

- `composed_factorization`: P(catastrophe) = Σ_ω ρ(ω)·binCDF(n_h, n_s, h_ω)·P(deployment catastrophe | ω).
- `joint_pass_prob`: per submission, P(both pass | x) = P(T misses x)·P(untrusted passes x). This conditional independence is a property of the game (fresh trusted coins), not a hypothesis.
- `composedEndToEnd`: if the trusted miss probability is at most τ on every bad submission, audit recall is at least r, and bad views are L-dominated by mediated honeypots, then for every colluding pair, P(catastrophe) ≤ (1 − r) + r·τ·L·(n_s+1)/(n_h+1).
- `composed_tight`: at n_h = n_s = 0, with τ = r = 1/2 and L = 1, the bound 3/4 is attained exactly.

Compared with the `min` corollary: with τ = 1/2, L = 1, n_h = 99, n_s = 0, the product gives (1 − r) + r·0.005, against min((1−r)+r·0.5, (1−r)+r·0.01).

Limits: τ is a worst case over bad submissions (Red picks the action that best evades `T`). The trusted monitor's own analysis (N1/N1b) is time-blind and certifies a different quantity, so this does not yet plug N1b certificates in directly. That needs a bridge from a TMCERT-style certificate to a per-submission miss bound τ. Novelty is modest: the product follows once independence is built into the game. The contribution is fixing a joint protocol in which multiplying is sound, and machine-checking it.


## Candidate statement

Suppose the same run has two sound safety analyses for the same catastrophe event `C`:

- a trusted-monitoring analysis gives `P(C) ≤ B_T` for every allowed Red strategy;
- an untrusted-monitoring analysis gives `P(C) ≤ B_U` for every allowed colluding pair.

If the combined protocol's adversary class is contained in both analyses' quantified classes and both bounds refer to the same event under the same joint experiment, then `P(C) ≤ min(B_T, B_U)`. This follows by taking the stronger of two upper bounds. A product bound does not follow from these marginal guarantees.

## Why multiplying the bounds needs more structure

Let one latent fair bit `Z` determine both monitors' failure events: trusted monitoring misses exactly when `Z = 1`; untrusted monitoring misses exactly when `Z = 1`. Each miss has probability `1/2`, but their joint miss has probability `1/2`, not `1/4`. Thus two marginal miss bounds of `1/2` only imply a joint bound of `1/2` absent a dependence condition.

Conditional independence given a fully specified attack/history could justify multiplying conditional miss probabilities, but averaging that product requires a common conditioning variable and uniform conditional guarantees. Adaptive Red observations, shared persistent randomness, or different event definitions can invalidate the proposed factorisation.

## Compatibility work required before formalisation

1. Define a joint protocol and one catastrophe event, including whether each monitor can halt, defer, or observe the other's transcript.
2. Identify a common adversary class. N1/N1b's time-blind attack model and UMPROTF1's shared-seed colluder with adaptive submissions are not automatically the same class.
3. State which existing bound applies pointwise to each combined strategy. If only marginal bounds survive, formalise the `min` corollary. Add a product result only with an explicit conditional-independence hypothesis and proof that it is preserved under the strategy quantifiers.
4. Keep monitor independence distinct from independence of the events “trusted monitor misses” and “untrusted monitor misses.” The latter is the condition relevant to multiplication.

## Source results

- N1/N1b: `<research-root>/control-tree/lean/ControlTree.lean` (not exported), sequential trusted monitoring with time-blind Red and the N1b dual certificate.
- UMPROTF1: `ledger/UMPROT.lean`, a honeypot screening phase followed by an untrusted-monitor deployment game, with its own shared-seed quantifiers and assumptions.

The immediate next step is to settle the joint protocol and adversary intersection. Until then, the only safe composition claim is the elementary `min` bound under the common-event/common-experiment conditions above.
