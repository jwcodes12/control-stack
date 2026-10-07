# Fidelity audit (orchestrator): UMNOGOF1, the coverage no-go (impossibility side of layer 1)

Statement: `ledger/UMNOGO.lean` as restated with Reviewer A's strengthening (frozen d251d71f8951). Depends on UMPROTF1.
Proof: 244 lines, isolated prover agent; gated, standard axioms. Red team (after restate): Reviewer A pass, Reviewer C pass. The
pre-restate Reviewer C verdict was discarded (red-team verdicts are now bound to the statement hash).

| element | classification | note |
|---|---|---|
| `IsKernel M`, `ContentPreserving M c` (exact decoder on supports) | SOURCE (strong) | No LLM summariser is proved to satisfy it. Deterministic canonicalisers do: by CANONF1 (ii), canon's output determines the ≈-class |
| `IsDist PH`; iid honeypots, global counter, **any** shutdown schedule κ ∈ [0,1] | SOURCE (the iid design family) | the stratified design (UMSTRATF1) is outside this family |
| `S` ⊆ Bad with pairwise distinct classes, k = \|S\| ≥ 1 | SOURCE | k counts Red-choosable bad classes surviving mediation |
| quantifier order: ∃ one deterministic pair, then ∀ n_h, κ, r, b, N ≥ 1 | stronger than the informal claim | one colluder defeats every parameterisation of the protocol |
| the generator is a point mass on a bad submission xs ∈ S | free-submission model | Red picks the task too. With an exogenous task stream the bound needs the task of xs to arrive; this is not formalised (DESIGN §2.1) |
| (b) exact attainment t·binCDF(n_h, n_s, t·p), r = 1, hard slack | SOURCE | |

**Reading.** For every iid honeypot law, a decodable mediator with k distinct bad classes admits a colluding pair
winning with probability ≥ (1−1/k)^{n_h}, which tends to 1 when k ≫ n_h.

**Composition with CANONF1.**
- Applying canon as the mediator, with content = ≈-class, satisfies the decoder hypothesis.
- So the verified canonicaliser *alone* cannot give a capability-free collusion guarantee once Red has many
  ≈-distinct bad programs to choose from. This is the formal version of "canonicalisation erases only the named
  channels".
- The step is a one-line corollary, not stated as a separate CID.

**Novelty.** Pigeonhole plus no-hit probability: elementary. The value is the precise impossibility statement for
untrusted monitoring. Empirical analogue: Greenblatt et al. Tables 4–5 (theming in real vs synthetic attacks).
