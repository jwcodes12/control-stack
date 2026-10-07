You are a HOSTILE REVIEWER of a proposed formal statement (campaign UMCERT) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art if available. Nothing in UMCERT is proved yet; this review
decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct,
why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not. The frozen, verified dependencies are below: PL_UMPROTF1 is the halting protocol of untrusted monitoring
with an upfront honeypot test (a FLAG with no audit left halts); PL_UMSTRATF1 is the stratified variant (content-only
mediator, m honeypots per bad class, class-aware hard slack).

WHY UMCERT. Final reviewers of the programme proposed, as the cheapest useful next step, a "certificate form" of the
UMPROT/UMSTRAT bounds: "if for all t in [0,1], binCDF(n_h, n_s, t)(1 - r + r min(1, L t)) <= U, then every colluding
pair has risk <= U". This replaces the Markov-type counting step h binCDF(n,s,h) <= (s+1)/(n+1) (loose: 0.154 vs
about 0.068 at m = 12, s_c = 1), lets the design-document numerics enter as Lean-checked rational certificates, and
makes explicit that at L = 1 the bound is two-sided (the honest-free floor max_h survH(h)(1 - r + r h) is the AOQL of
the single-sampling plan (n_h, c = n_s), Dodge-Romig). It is also the first milestone of a later, larger project: a
Lean certificate checker for stateful trusted-monitoring games (Games for AI Control, arXiv 2409.07985, Prop. 4.1),
sound against every history-dependent Red.

The draft goes further than the reviewers asked: (R) is an EXACT reduction of the worst case over all colluding pairs
(shared seed, adaptive generator) to one-shot stateless pairs, for every shutdown schedule kappa and budget b;
(S2) claims the stratified design's exact worst case is max_t binCDF(m, s_c, t)(1 - r + r t) under exact decoding.
Brute force in exact rationals (numerics/umcert_check.py): 300 random halting instances and 200 stratified
instances (random kernels, schedules, budgets, history-dependent generators) with 0 violations of the per-seed
reduction; survH antitone on 400 random schedules with 0 violations; the 14-point Witness grid passes with min
slack 0.00108; binCDF(12,1,1/8)/8 = 0.06834 >= 17/250.

CHECK IN PARTICULAR
1. TRUTH of every conjunct, including edge cases: empty Bad; N = 0 (excluded where stated, included in (C) and
   (S1)); b = 0; r in {0,1}; kappa with values 0 or 1; U < 0; g negative or non-monotone in (C); t in {0,1};
   empty Es; Es containing untested-by-Bad classes; n_h = 0; m = 0; s_c >= m. Are the 0 <= U hypotheses needed
   where present and sufficient where absent? Is (C) true for N = 0 and empty Bad?
2. Is (R)'s RIGHT side the right one-shot quantity (E (push M PH) psi is the honeypot pass rate; capB uses the bad
   view's pass rate E (M x) psi)? Is the iff genuinely exact for b = 0 (an unaffordable flag halts, so the one-shot
   value is S * E(M x) psi)? Does quantifying over (Omega : Type) inside an iff create any encoding trap?
3. Is (S2) right (exactness needs a colluder that PASSes only the decoded attack class at rate t, so every other
   tested class has pass rate 0 and binCDF(m, s_c, 0) = 1)? Is "independent of the kernel K and the number of
   classes" a fair reading? Does (S1) really need no coverage hypothesis?
4. (G) grid lemma: hypotheses sufficient? Is GridCert well-formed (head? = some 0, getLast? = some 1, GridOK on
   consecutive pairs)? Should it instead take a computable rational checker (decide) or Bernstein coefficients?
   Will the Witness be provable by norm_num in reasonable time (degree 12 at denominators 100)?
5. FIDELITY and OVERCLAIM in the docstring: "shared randomness, history dependence and waiting do not help the
   colluders", "the worst case is a function of the trusted components only", "exact". Is any of that false or
   misleading (e.g. it is relative to the modelled class: stateless monitor, constant recall, halting protocol)?
6. DECISION RELEVANCE: what does a lab gain beyond UMPROT/UMSTRAT? Is the improvement in the certified number
   (0.154 -> 0.075 at the instance; DESIGN tables) worth a CID? What would make it more useful (e.g. a soft-slack
   instance, a hockey-stick instance, the n_h = 100 DESIGN table rows)?
7. NOVELTY vs prior art (acceptance sampling AOQL, Dodge-Romig; Games for AI Control; Ctrl-Z App. E; LASR
   2602.20628 App. B); verify every id you cite.
8. LEAN ENCODING: provability; the right helper lemmas; whether any conjunct should be split or dropped.

End with an overall verdict (accept / minor / major / reject), the fixes in priority order, and the final list of
conjuncts you would freeze.

