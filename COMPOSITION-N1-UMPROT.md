# Design note: composing trusted and untrusted monitoring

**Status:** scope and probability bookkeeping only; no composition theorem is claimed.

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

- N1/N1b: [`../control-tree/lean/ControlTree.lean`](../control-tree/lean/ControlTree.lean), sequential trusted monitoring with time-blind Red and the N1b dual certificate.
- UMPROTF1: `ledger/UMPROT.lean`, a honeypot screening phase followed by an untrusted-monitor deployment game, with its own shared-seed quantifiers and assumptions.

The immediate next step is to settle the joint protocol and adversary intersection. Until then, the only safe composition claim is the elementary `min` bound under the common-event/common-experiment conditions above.
