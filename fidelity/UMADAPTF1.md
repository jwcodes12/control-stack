# Fidelity audit (orchestrator): UMADAPTF1, a converse for adaptive honeypot testers

Statement: `ledger/UMADAPT.lean` v1 (frozen a416cc05f830). Depends on UMLOWERF1 (and UMHSF1, UMSURVF1, UMPROTF1).
Proof: 484 lines (isolated prover agent), gated, standard axioms. Session 3 precursor 2 (Reviewer B's order).

History:
- **v0**: contract "keep = 1 on every all-FLAG history"; (a) t(1 − tn/k); arithmetic (b); a pointwise counterexample
  (c) described as "the multiplier cannot be kept".
  - Reviewer A: UMADAPT minor. The proof idea must use a REFERENCE (forced-FLAG) experiment, not conditioning on FLAG;
    the contract is sufficient, not weakest; (c) refutes the formula only pointwise; a 4-class lock-on tester defeats
    the optimised floor; a sharper balanced bound exists (numerically = the DP optimum).
  - Reviewer B: minor; U1 (MAJOR) the same overclaim of (c); (b) was detached arithmetic; a 3-class sticky tester gives
    t − t³ + t⁴/3 < 1/2 for every t; a necessity witness for the contract.
- **v1**: contract `AcceptsAllFlag` (the reference experiment accepts w.p. 1) with (s) as a sufficient condition;
  (a) with max(0, ·); (a') the risk-valued optimised corollary; (c1) pointwise at t = 3/4 and at the corollary's
  t = 2/3; (c2) the sticky tester for every t; the necessity witness. Reviewer A and Reviewer C passed.

| element | classification | note |
|---|---|---|
| `adSurv`, `adProtocolCat` | MODELLING | next honeypot law from the full test history (honeypots, views, answers); final randomised keep; the colluders do not see the test; halting deployment |
| `AcceptsAllFlag` | SOURCE: the contract | weakest natural form; load-bearing (Witness: rejecting the perfect record gives 1/8 < 3/8) |
| (s) | SOURCE | keep = 1 on all-FLAG histories suffices: every miss-only slack rule accepting zero-miss records |
| (a) risk ≥ t·max(0, 1 − tn/k) | SOURCE | identical until bad against the forced-FLAG reference experiment; for the UMLOWERF1 pair only, not the minimax risk |
| (a') min(1/2, k/(4n)) at t = min(1, k/(2n)) | SOURCE | budget linear in k for every adaptive tester; n_s multiplier lost |
| (c1) | SOURCE, pointwise | refutes the UMLOWERF1 formula at fixed t (141/512 < 21/64; 26/81 < 1/3); NOT after re-optimising t (≈ 0.346 > 1/3) |
| (c2) | SOURCE | refutes UMLOWERF1's optimised nonadaptive value for every t: t − t³ + t⁴/3 < 1/2 |

**Reading.** The nonadaptive restriction of UMLOWERF1 is necessary: adaptive testers beat its formula, even after the
colluder optimises t. What survives for every adaptive tester that accepts an all-FLAG monitor is budget ∝ k (number of
decodable bad classes), without the (n_s+1) factor. The multiplier is genuinely lost for n of the order of k(n_s+1)
or smaller and nearly recovered for n ≫ k(n_s+1) (Reviewer B numerics). Reviewer A's sharper balanced bound
(t/k)[(k − a)(1 − t)^q + a(1 − t)^{q+1}] (attained by a balanced nonadaptive schedule under the contract alone) is not
in Lean.

**Novelty.** Classical technique (Shoup's difference lemma, ePrint 2004/332; hard-distribution lower bounds); modest
infrastructure. No source found stating this honeypot-budget converse.
