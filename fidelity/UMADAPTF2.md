# Fidelity audit (orchestrator): UMADAPTF2, sharp converse for adaptive honeypot testers

Statement: `ledger/UMADAPT2.lean` v1 (frozen cf874653d2fa). Depends on UMADAPTF1 (and transitively UMLOWERF1, UMHSF1,
UMSURVF1, UMPROTF1). Proof: 1469 lines, gated (claim and witness), standard axioms. Session 8.

Provenance: the sharper balanced bound was first flagged numerically by Reviewer A in the UMADAPTF1 design review and
recorded, unclaimed, in the UMADAPTF1 docstring. Session 6/7 proved it as a proofport (`conv_a_sharp`) against the
UMADAPTF1 definitions without a ledger event; session 8 registered it as a separate form, reusing that port verbatim
(F1's `claim`/`witness` renamed) and adding the Setup-to-decoder wrapper and the witness.

Red team: Reviewer A pass, Reviewer C pass (both foreign to the author). Neither found encoding bugs. Reviewer A notes
a prose imprecision: the docstring says the bound "stays positive for every n when t < 1"; this needs 0 < t < 1 (at
t = 0 it is 0). The Lean statement is unaffected; recorded here rather than restated.

| element | classification | note |
|---|---|---|
| quantifiers, contract, colluding pair | SOURCE: identical to UMADAPTF1 (a) | reuses `Setup`, `AdTester`, `AcceptsAllFlag`, `adProtocolCat`, `seedLaw`, `classRule`, `seedPolicy` |
| `sharpTarget k n b` | SOURCE | (k − a)·b^q + a·b^{q+1}, q = ⌊n/k⌋, a = n mod k: the balanced minimum of Σ b^{m_ω} under Σ m_ω ≤ n |
| Claim: (t/k)·sharpTarget(k, n, 1 − t) ≤ risk | SOURCE | implies UMADAPTF1 (a) by Bernoulli; non-trivial for n ≥ k/t where (a) is 0 |
| Witness | SOURCE | k = 2, n = 3, t = 1/2: bound 3/16 > 1/8 (F1); the round-robin nonadaptive tester attains 3/16 |

**Reading.** For the UMLOWERF1 colluding pair, adaptivity buys the tester nothing beyond balancing: the risk floor is
roughly t(1 − t)^{n/k}, attained (at the witness instance) by a nonadaptive round-robin schedule. A general attainment
theorem is not claimed. Classical technique (identical-until-bad, Shoup 2004; convex balancing/majorization).
