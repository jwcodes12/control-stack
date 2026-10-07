You are a HOSTILE REVIEWER of a proposed formal statement (campaign TMCERT) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art if available. Nothing in TMCERT is proved yet; this review
decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct,
why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not. The programme so far is mostly untrusted monitoring with honeypots (UMPROT etc.); TMCERT starts the
trusted-monitoring layer.

WHY TMCERT. Two final reviewers ranked first "(A) rescoped: a certificate checker for a finite stateful
trusted-monitoring model, with explicit adversary observations and uncertainty in the conditional transitions.
Soundness: for a fixed Blue controller, a valid risk certificate bounds the catastrophe probability for EVERY admissible
history-dependent Red and every admissible transition model; a separate certificate lower-bounds honest useful reward.
First instance: Games for AI Control (GAC, Griffin, Thomson, Shlegeris, Abate, arXiv 2409.07985) Prop 4.1. GAC's Red is
memoryless with a fixed beta: show exactly when that is without loss of generality, and give a counterexample when Red
sees more." One reviewer suggested the certificate shape "for all n s a, immediateCat s a + sum_s' safeContinue s a s'
V n s' <= V (n+1) s".

DRAFT DESIGN. (T1) Bellman-supersolution soundness against seeded, history-dependent Reds that see the full state
history (so every observation-restricted Red is covered) and against a history-dependent choice among admissible
models (nature). (T2) Tightness: Vstar (max over Red actions) is the least certificate and is attained by a
deterministic Markov full-information Red. (T3) Honest usefulness: sub-solutions lower-bound the expected reward of the
honest Markov chain. (T4) The GAC game (state = coins; thresholds enter as zone probabilities TA, TD, FA; audit with no
coin runs the code, as GAC states) is lawful; GAC's sup over beta is a sound certificate for SEEDED memoryless Reds.
(T5) Counterexample: a Red that knows only the round index (blind, clocked) beats every fixed beta, 5/8 vs 49/160, at a
2-problem, 1-coin instance; it equals the full-information value. Numerics (float, numerics/gac_realistic.py) at GAC's
scale, 100 problems and 2 coins, GAC's Beta(7.39, 6.86) / Beta(8.91, 2.82) score laws, constant audit FPR 2% while
coins remain, defer FPR 10%: best fixed beta 0.36, "backdoor only the last 13 problems" 0.67, full information 0.71.
Exact-rational toys (numerics/gac_explore.py, gac_small.py): gaps at every tested instance.

CHECK IN PARTICULAR
1. TRUTH of every conjunct and the Witness; edge cases (N = 0; Lawful with mass < 1; empty Theta; A with one element;
   negative V; nature's selector depending on the seed; C = 0).
2. Is `risk` (Red's policy sees states, which in GAC Red does not observe) the right object for "every history-
   dependent Red"? Does seeding plus behavioural randomisation cover every mixed strategy? Does the nature selector
   model "uncertainty in conditional transitions" faithfully, or should the uncertainty be a fixed-but-unknown model
   (a weaker adversary) with a separate statement?
3. Is `gac` faithful to GAC §4 / App. C (state, coins, audit/defer/run zones, audit with no coin -> run, audit of a safe
   solution uses a coin, defer continues, caught backdoor -> safe sink)? GAC's Blue thresholds depend on (m, c); is
   folding them into TA/TD/FA as functions of (n, c) faithful? Is the indexing (n = remaining minus one) right?
4. Is (T4) the right "exactly when" statement? It only says sup_beta is sound for seeded memoryless Reds. What would
   a real "exactly when" theorem be (e.g. stationary games where memoryless is w.l.o.g.; or: Red's information is
   independent of state and time)? Is the T5 counterexample a fair objection to GAC, given that in AI control the
   untrusted model handles each task in a fresh context (no memory, possibly no clock)? Is "the round index" a
   realistic observation (timestamps, task ids, codebase state)?
5. Decision relevance and NOVELTY: is the clock objection to GAC's memoryless Red known (GAC itself, Ctrl-Z
   2504.10374, "subversion via focal points", Mallen et al., "How to evaluate control measures"/Korbak et al., the
   "AI control safety case" literature, Bhatt et al.)? Verify ids you cite.
6. LEAN ENCODING: provability of (T2) (Finset.sup' over univ; constructing an argmax policy that depends on
   h.length); Fin arithmetic in `gac`; the Witness certificate exV (is it really a certificate for all n?).
7. What is missing for the certificate checker to be useful at GAC's scale (a computable rational checker with a
   soundness bridge, interval models for an estimated ROC, a usefulness certificate for GAC)?

End with an overall verdict (accept / minor / major / reject), the fixes in priority order, and the final list of
conjuncts you would freeze.

