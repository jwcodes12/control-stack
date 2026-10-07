# Fidelity audit (orchestrator): UMDEFERF1, audit-then-defer after exhaustion

Statement: `ledger/UMDEFER.lean` v2.1 (frozen ad82ec06fc48). Depends on UMPROTF1 (and UMHSF1, UMSURVF1). Proof: 714 lines (isolated prover agent), gated, standard axioms.

History:
- **v1** got major revision from Reviewer A:
  - the deferred-item audits were uncharged;
  - q·r needed a conditional floor, not an average (a deployment-wide-coin counterexample);
  - the asymptotic prose was false;
  - the no-go was over-scoped;
  - the stopping ratio is prior art (Shlegeris, Nov 2024).
- **v2** introduced the finite retry certificate (`retry`, `finiteCap`), the protocol certificate, the no-go for
  every two-point honeypot law, and the corrected limit. On v2, Reviewer A said revise: the conditional floor was
  only a comment. Reviewer C passed. Reviewer B's review: minor (≈ 170,000 exact checks, 0 counterexamples).
- **v2.1** adopted Reviewer A's service-dependent `catV` with reachability (`Reach`) and `UniformFloor`, and Reviewer B's
  docstring fixes and limit conjunct. Reviewer A and Reviewer C both passed (hash-bound).

| element | classification | note |
|---|---|---|
| `catV` (service `a h x z`), `catD` = the constant-α special case | MODELLING | while u < b it is the halting protocol of UMPROTF1. At u ≥ b: halt w.p. η; else defer (no catastrophe); a deferred bad submission ends safely w.p. a h x z |
| `UniformFloor` over `Reach` | SOURCE: the conditional contract, now a theorem's hypothesis | the floor is required only on reachable, positive-probability, exhausted-budget bad flags. An average rate does not satisfy it (Reviewer A's counterexample) |
| unmetered audit service | MODELLING (stated) | load is adversary-controlled, up to q(1 − η)N; a reserve-halting variant is safer (Reviewer B numerics). Not charged to b |
| replacement contract | MODELLING (stated) | no effect before execution; the replacement is complete and safe; shutdown is immediate |
| (a) η = 1 recovers `cat`/`protocolCat`; 0 ≤ catV ≤ 1 | SOURCE | fidelity anchor to the frozen core |
| (b) catD ≤ finiteCap for every θ ∈ [0,1] | SOURCE | the exact worst case: attained in 4000/4000 Bellman checks (Reviewer B) |
| floor bridge: catV ≤ catD under the floor | SOURCE | it carries every bound to the actual service |
| (c) attainment at an EXHAUSTED budget, closed form, ratio, limit | SOURCE | the informal synopsis in `form.json` says "attained by always-attack" without the exhausted-budget qualifier. That is false before exhaustion (Witness 1/10 < 29/200) and must not be banked (Reviewer A) |
| (d) protocol certificate for the actual service; coarse corollary | SOURCE | sufficient conditions only. The coarse q ≥ H/ε (≈ 0.6 in the example) is loose; the finite certificate needs θ ≈ 0.32 (Reviewer B). With b ≥ 1, no target below 1 − r is reachable |
| (e), (e') no-go | SOURCE, scoped | two-point space; free submission without a benign-flag guard (Greenblatt App. G and LASR inverse honeypots are guards); not a necessity theorem for incrimination |

**Reading.** In the halting core, honeypots protect because catching or halting ends the game. If unaffordable flags
merely defer, the honeypot guarantee survives only with a uniform stopping hazard θ on deferred attacks, and its
honeypot term grows by up to 1/θ. Without such a hazard, a burn-then-attack colluder's risk tends to 1 over long
horizons, against every two-point honeypot law. In a safety-only model halting dominates deferral; deferral buys
availability, which is not modelled.

**Witness.** A genuinely history-dependent service (3/4 at the root, 1/2 later) gives 49/400, below the floor envelope
29/200. Two-round retry suppression: 29/200 with α = 1/2 versus 19/100 with α = 0. A protocol-level instance gives
35721/400000. A certificate instance and the no-go value 3/16 are also included.

**Novelty.** The win/continue/lose ratio is Shlegeris's (Redwood, Nov 2024) and LASR's u/(c+u). Defer is a Blue action
in Games for AI Control; Ctrl-Z covers incrimination by resampling. Claimed: the adaptive-generator Lean bound with a
reachable conditional floor, the budget-sensitive finite certificate, the composition with the honeypot test, and the
two-point no-go. Calibrated: modest infrastructure.

**Scope notes (Reviewer A, final review 2).**
- The floor bridge ASSUMES the conditional contract; it does not derive it from an average audit rate or from
  "fresh coins". Deriving α = q·r needs a conditional recall floor for the selected audits.
- The resource prose describes the expected load under a selection service. A reserve-halting variant is not in the
  frozen Claim; its monotonicity is numerics only.
