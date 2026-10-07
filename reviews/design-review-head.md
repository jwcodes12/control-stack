You are a HOSTILE REVIEWER of a formal-model design document for AI control. Do not praise; find errors. Use web
search where useful (e.g. to check prior art and the LASR / Greenblatt et al. protocols). For each issue give: severity
(FATAL / MAJOR / MINOR), the exact sentence, definition or number it concerns, why it is wrong, unfaithful or
overclaimed, and a concrete fix.

The authors want Lean-verified, CAPABILITY-FREE guarantees: theorems of the form "for every policy the untrusted model
could follow, P(unaudited catastrophe) <= X" with X a function of trusted components only. They accept classical
lemmas as infrastructure, but not vacuity, falsity, or unfaithfulness. Nothing is formalised yet; this review decides
what gets formalised.

Check in particular:
1. FAITHFULNESS to Redwood/GDM-style untrusted monitoring (Greenblatt et al. 2312.06942; LASR 2602.20628; Shlegeris'
   collusion posts). Is anything essential missing or mis-modelled: the monitor's view, the shared seed, statelessness
   (A1/A2), upfront vs interleaved honeypots, the audit / budget / halt rule, honeypot passes vs flags, the trusted
   monitor, defer-to-trusted, attack selection, the generator seeing the honeypot outcome, multi-step attacks? Is the
   kill-schedule treatment of slack (hard vs LASR soft) right, and is "every pass counts" the right capability-free
   choice?
2. TRUTH of each target theorem T1-T6 as stated (including edge cases: h=0, n_s >= n_h, kappa=0, r<1 interacting with
   the budget, empty Bad, q with zero entries, eta<0, the 'halt on budget exhaustion' semantics, infinite L). Try to
   construct counterexamples, especially to T3a (first bad attempt decides), T3 (closed forms), T4c (floor), T5b/T5c
   (exact minimax value; is uniform-over-classes really optimal when classes have different numbers of members or
   when the mediator K is randomised?), T5d (constant (1+e^eta) gamma), T6 (is canon p = canon q <-> p ~ q achievable
   with the stated generators; does C-style for-loop desugaring preserve semantics; alpha-renaming in an imperative
   language with uninitialised variables).
3. NON-VACUITY: is X small at realistic parameters, or is delta trivially ~1 for every mediator anyone would deploy?
   Is the authors' 'coarse regime' argument (section 5) honest, or does it make the untrusted monitor pointless? Is
   there a better capability-free quantity than worst-case hockey-stick / likelihood ratio that is non-vacuous for
   rich mediators (e.g. something exploiting that Red's generator must ALSO produce a working attack, or randomised
   honeypot construction from deployment outputs)? If the honest answer is "no capability-free guarantee is possible
   for rich content", say so and say whether the floor theorem T4c is the right formalisation of that impossibility.
4. NOVELTY / prior art for each theorem (DP hockey-stick bounds, binomial order-statistic identity, the
   capacity/semantic-entropy bounds of Motwani et al. 2402.07510, collusion-free mediated protocols
   (Alwen-shelat-Visconti), Cachin's stego security). Classical is acceptable as infrastructure; just name it.
5. NUMBERS: recompute any number you can (tables in section 5, the LASR-parameter values in section 6).
6. Lean feasibility: are the definitions sketched (finite sums, recursive surv/cat over histories) the right encoding,
   or will they make proofs needlessly hard or statements unfaithful?

End with an overall verdict (accept / minor / major / reject), the five most important fixes, and a revised list of
theorems you would formalise first.

=== DOCUMENT 1: DESIGN.md ===
