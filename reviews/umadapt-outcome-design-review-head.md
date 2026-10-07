You are a HOSTILE REVIEWER of two proposed formal statements in a Lean-verified AI-control programme: campaign UMADAPT
(a ledger statement, Lean v4.35 + Mathlib) and the VCVio outcome-valued game (`ControlStack/Outcome.lean`, Lean v4.34
+ VCVio, not ledger-gated). Do not praise; find errors. Use web search for prior art if available. Nothing is proved
yet; this review decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact
definition or conjunct, why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not.

PART 1: UMADAPT. The frozen, verified PL_UMLOWERF1 (below) lower-bounds the risk of every NONADAPTIVE joint honeypot
design by t(1 - t n/(k(n_s+1))) for one explicit colluding pair (uniform seed on k bad submissions in distinct
decodable classes; the monitor PASSes the decoded seed class w.p. t; the generator submits the seed). A final
reviewer computed exact optimal ADAPTIVE testers by DP and found they beat that formula (by 1.3-1.7x at the
colluder's best t), and sketched an identical-until-bad converse t(1 - t n/k) for adaptive testers. UMADAPT states it,
with the optimised corollary min(1/2, k/(4n)) and an explicit counterexample showing the (n_s+1) factor cannot be kept.
Brute force (numerics/umadapt_check.py, exact rationals): DP-optimal adaptive testers (both the all-FLAG contract and
the <= n_s contract) on 36 cells (k in 2..5, n <= 8, n_s <= 2, t in {1/4,1/2,3/4,1}) never go below t(1 - t n/k);
the bound is attained at (k, n, n_s) = (2, 1, 0); the Lean counterexample tester gives 141/512 at t = 3/4.

CHECK (UMADAPT)
1. TRUTH of (a), (b), (c) and the Witness, edge cases: n = 0; k = 1; t in {0,1}; r in {0,1}; b = 0; N = 1;
   testers that query benign items or items outside S; keep depending on views; histories with honeypots outside S.
2. Is the contract (keep = 1 on every all-FLAG record) the right weakest contract? Is it satisfied by realistic
   slack rules, and is "fails for inverse honeypots / benign-flag guards" right? Is it a problem that keep is only
   applied at the end (early shutdown modelled as keep = 0 on every continuation)?
3. Is the model of an adaptive tester general enough (T sees honeypots, views and answers; randomised; keep
   randomised)? Does the deployment (halting protocol, colluders do not see the test) matter for the lower bound?
4. Quantifier order: the decoder g is chosen before the tester; t, r, b, N after. Is the colluder legitimately
   fixed before the tester (the bound holds for every t)?
5. Is (c) a convincing counterexample (t = 3/4 is not the colluder's best t against that tester)? Should it be at the
   best t, or is "the PL_UMLOWERF1 formula fails pointwise in t for adaptive testers" the right claim?
6. NOVELTY (Shoup's difference lemma; Yao; adaptive group testing; acceptance sampling with curtailment/sequential
   sampling, Wald SPRT): is the converse known in the testing / property-testing literature? Verify ids you cite.

PART 2: outcome-valued game (VCVio). The existing `Refinement.lean` (below) proves the Boolean catastrophe game equals
the core recursion `catG`, factorises through the seed, and gives an end-to-end bound. Its Boolean outcome merges
completion, caught shutdown, test rejection and budget halt, so it cannot speak about availability; the frozen
PL_UMUSEF1 docstring's "operational bridge for both" overstated. `Outcome.lean` returns one of five outcomes.

CHECK (Outcome)
7. Is `deployO`/`gameO` faithful to `deploy`/`protocolGame` (same branch structure) so that MarginalClaim is true?
   Are caughtG, haltP (textual copy of PL_UMUSEF1.haltP) and complG the right recursions? Is PartitionClaim true
   with only kernel/law hypotheses (no [0,1] constraint on phi or R)?
8. Is HonestClaim true (iid benign stream, seed-free honest monitor), including b >= N, N = 0, n_s >= n_h,
   alpha0 in {0,1}? Is the link to PL_UMUSEF1 (b) (honestCompletion = binCDF(n_h, n_s, missRate) * binCDF(N, b,
   flagRate)) genuinely by textual identity of the definitions, or does it need an argument about how missRate and
   flagRate correspond to Pr[...] of ProbComps?
9. Is TwoMarginalsClaim meaningful, or merely a conjunction of two independent facts? What operational statement
   would actually couple safety and availability in one experiment (e.g. an operational form of PL_UMUSEF1's
   identity D * risk = q * completion for the view-blind pair, or a Pareto statement)?
10. Witness numbers.

End with an overall verdict for each part (accept / minor / major / reject), the fixes in priority order, and the
final list of conjuncts you would freeze.

