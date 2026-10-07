# Fidelity audit (orchestrator): UMCERTF1, certificate form of the UMPROT/UMSTRAT bounds

Statement: `ledger/UMCERT.lean` v1 (frozen 73c2633b1568). Depends on UMPROTF1 and UMSTRATF1 (and UMHSF1, UMSURVF1).
Proof: 750 lines (isolated prover agent, one lemma per conjunct), gated, standard axioms. Session 3 precursor 1 (Reviewer B's order).

History:
- **v0** (draft): (R), (C), (E), (G0), (G), (F), (X), (S1), (S2) and a 14-point Witness.
  - Reviewer A: major, no false conjunct. Overclaims: blanket "EXACT"; the trusted-input list omitted Bad; "history
    dependence does not help" unscoped; AOQL identification too broad; (S1) "no coverage" hid the c x ∈ Es hypothesis.
  - Reviewer B: minor (≈ 10^5 exact checks, 0 violations). Add end-to-end grid statements (CG)/(SG), the refinement (D),
    exactness at realistic L (Xp); drop `1 ≤ b` from (S2); a tighter and broader Witness.
- **v1** applies all of it. Reviewer A and Reviewer C both passed (hash-bound), no binder repairs.

| element | classification | note |
|---|---|---|
| `capB r b a` | SOURCE | one attack's value: 1 − r + r·a with an audit, a at b = 0 (halt) |
| (R) one-shot reduction (iff) | SOURCE, scoped | exact within the halting model; generator history and finite seed mixtures do not raise the worst case. Not for non-halting variants or phase-aware monitors (A1). `0 ≤ U` is needed only for empty Bad |
| (C) envelope certificate | SOURCE | sound upper bound for any envelope; not exact for a given mediator (Reviewer A: L = 2 example, 1/2 vs 3/8) |
| (E) L-domination and hockey-stick envelopes | SOURCE | the two trusted-side hypotheses of UMPROT T3 |
| (G0) survH antitone in the pass rate | SOURCE | every κ ∈ [0,1]; survH is NOT antitone in the miss index |
| (G), (CG), (SG) grid certificates | SOURCE | finite rational checks; (CG) needs a monotone nonnegative envelope |
| (D) refinement | SOURCE | the counting bounds satisfy the certificate hypothesis: never worse than UMPROT T3 (hard and soft slack, every b) |
| (F) view-blind floor | SOURCE | = UMUSE (c') + (R)(→). AOQL (large-lot, Dodge–Romig) only for hard slack with r = 1 or b = 0 |
| (X) exactness at L = 1 | SOURCE, degenerate regime | L = 1 forces M x = push M PH: perfect honeypots |
| (Xp) exactness, decodable content-only M, min class mass p | SOURCE | exact worst case of the global-slack design at uniform honeypots (p = 1/k): DESIGN §5 "global" column |
| (S1)/(S2) stratified certificate and exactness | SOURCE | (S2) needs exact class decoding (non-decodable control: 0.0452 < 0.0683); any b; |Es| enters only the cost m·|Es| |

**Reading.** In the halting protocol the worst case over every colluding pair is the worst one-shot pair, a function of
(M, PH, κ, n_h, r, Bad, [b > 0]). It is computable from trusted components by a one-dimensional sup over the honeypot
pass rate, and certifiable by a finite monotone grid. The certificate is exact for perfect honeypots, for decodable
content-only mediators with coverage p, and for the stratified design under decoding. It is never worse than the
counting bound, and typically 2–3× tighter: at m = 12, s_c = 1 the certified 0.07 against the counting bound 0.154
(the exact value is 0.06834); soft slack n_h = 100, n_s = 5: 0.019 against 0.0495; L = 4, r = 9/10, n_h = 30, n_s = 1:
0.17 against 0.332. At the DESIGN §5 row (n_h = 100, n_s = 8, k = 16) the counting bound is vacuous (1.43) and the
exact value 0.827 (numerics only; not a Lean fixture).

**Witness.** Three grid fixtures with attaining points: the m = 12 bracket [0.06833, 0.07] for both designs (explicit
pairs), soft slack, and the kink/imperfect-recall fixture. (Xp) with p < 1 is not instantiated by the Witness (Reviewer A,
minor; the hypothesis class is inhabited: Bool, uniform honeypots, p = 1/2).

**Novelty.** Classical: first-bad-decides plus a reduction to one-shot pairs; monotone rectangle bounds; acceptance
sampling (Dodge–Romig AOQL). The value is that design tables become Lean-checked certificates; it is the first
milestone of the certificate-checker direction (A).
