# Fidelity audit (orchestrator): UMLOWERF1, a converse for nonadaptive joint test designs

Statement: `ledger/UMLOWER.lean` = Reviewer A's fixed text, restated (frozen 8415ec049329). The original statement (a superseded draft)
is not included in this export. Depends on UMPROTF1 (`cat`, `Hist`) and UMHSF1 (`IsKernel`, `IsRule`,
`IsDist`, `ContentPreserving`). Proof: 284 lines (`proofs/UMLOWERF1.lean`), adapted from the proof of the original
statement; gated, standard axioms.

Red-team history:
- Original text: Reviewer A **revise** and Reviewer C **revise**, for the same reason. The colluder `(ρ, φ, π)` was
  existentially quantified *after* the design `D` and the rule `keep`, so a prover could tailor it to the design
  (Reviewer C: e.g. attack a class that the design leaves uncovered). Reviewer A also flagged the unqualified Θ wording.
- Restated text: Reviewer A pass and Reviewer C pass, both bound to the frozen hash.

| element | classification | note |
|---|---|---|
| `Setup`: kernel M; content-preserving for c (an exact decoder); S ⊆ Bad; c injective on S; S nonempty | SOURCE | k = \|S\| distinct decodable bad classes. Reviewer A checked that the decoder and injectivity are load-bearing: removing either gives risk 1/32 or 1/128 < 1/4 at the witness parameters |
| `∃ g` (the decoder) chosen **before** n, n_s, D, keep, t, r, b, N | SOURCE (the fix) | the colluder depends only on (S, c, g, t). It is the same pair against every design and rule |
| `TestSetup`: D any law on n-tuples; keep ∈ [0,1]; keep = 1 whenever there are ≤ n_s misses | SOURCE | covers correlated, stratified and deterministic designs, and global or class-aware slack. D has no seed argument, so the design is independent of the seed (A3) |
| `designSurv` | MODELLING | given the tuple, PASS events are independent with probability a(x) = Σ_z M x z φ z (fresh stateless calls, A1). It is the design-level generalisation of `surv` |
| strategy: `seedLaw S` (uniform on S); `classRule c g t` (PASS the decoded seed class w.p. t); `seedPolicy` (submit the seed) | SOURCE (now explicit) | the conclusion also certifies that these are a law, a rule and a policy |
| conclusion: t(1 − t n/(k(n_s+1))) ≤ designProtocolCat, for all r ∈ [0,1], b, N ≥ 1 | SOURCE | there is no Θ claim in the Lean. The docstring says the matching upper bound needs the separate hypotheses of UMSTRATF1/UMPROTF1 |

**Reading.**
- Against every NONADAPTIVE honeypot design and every slack-respecting shutdown rule, a decodable mediator with k bad classes
  admits a colluder with risk ≥ min(1/2, k(n_s+1)/(4n)). This is for n > 0, at t = min(1, k(n_s+1)/(2n)).
- With UMSTRATF1 (fixed per-class budget m = n/k, class-aware slack, content-only mediator), honeypot budget per
  distinguishable class gives order-of-budget scaling (lower and upper bounds under their respective hypotheses). **This holds only under UMSTRATF1's
  hypotheses**, and only for the adversarial gain: at r < 1 and b ≥ 1 the always-flag floor 1 − r remains (Reviewer A).

**Witness.** Four classes, one honeypot of each (deterministic stratified design), zero slack, r = 1, b = N = 1,
t = 1/2. The bound 1/4 is attained exactly. Non-degenerate: the seed is uniform over four values and the monitor
randomises.

**Novelty.** Markov's inequality over a uniform seed (both red teams; Blum–Hopcroft–Kannan Thm 2.1). As a converse for
honeypot-based untrusted monitoring, neither red team found it stated, in Greenblatt et al. 2312.06942 or in LASR
2602.20628. Calibrated: elementary infrastructure; the value is that it makes layer 1 two-sided.

**Scope note (Reviewer A, final review 2).**
- `D` samples a whole tuple, independently of the seed. So the converse covers NONADAPTIVE joint designs only. An
  adaptive tester that picks later honeypots from earlier answers can do better: with four decoded classes, t = 1,
  n_s = 1 and five tests, scanning until the first PASS and then repeating that class gives risk 0 < 3/8.
- `TestSetup` requires continuation on every pattern with ≤ n_s misses. Extra rejection rules (e.g. inverse
  honeypots) need not satisfy that contract.
