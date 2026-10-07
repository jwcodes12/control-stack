PROGRAMME CONTEXT. We are building a Lean-verified, CAPABILITY-FREE guarantee stack for AI control (Redwood/GDM-style
untrusted monitoring): theorems of the form "for every policy the untrusted model could follow, P(uncaught catastrophe)
<= X" with X a function of explicit parameters of trusted components (mediator kernel M, honeypot law P_H, shutdown
schedule, n_h, audit recall r, catastrophe set Bad). Design document (hostile-reviewed by Reviewer A-Reviewer A and
prover agent-Reviewer B; all core inequalities judged true; v1 incorporates every fix): <research path>
Model in one paragraph: submissions x in a finite X; a trusted mediator kernel M : X -> Z -> R gives the monitor's whole
view z; the untrusted monitor is a stateless rule phi : Z -> [0,1] (prob. of PASS) depending on a shared seed omega with
the generator; the generator is any history-dependent randomised policy; an upfront test runs n_h iid honeypots from
P_H (a PASS on a honeypot is a miss; the (j+1)-th miss shuts down with prob. kappa_j); then N deployment rounds: PASS on
a bad submission = catastrophe; FLAG uses an audit while u < b (bad caught w.p. r, else executes), FLAG with no audit
left halts (safe).

JOHN'S OVERRIDE (programme owner): classical lemmas are WELCOME as infrastructure for the stack. Triviality alone is
NOT a reason to kill these formulations; report novelty honestly in "trivial_tool"/"known_refs" but judge the verdict
on FIDELITY (does the Lean say what the informal claim says, with no excess or missing binders, no wrong-reason truth),
VACUITY (are the hypotheses jointly satisfiable non-trivially; is the Witness meaningful) and FALSITY (is any conjunct
false? try counterexamples, edge cases: empty Bad, zero entries, h=0, n_s >= n_h, r in {0,1}, b=0, N=0, eta<0).
QUESTION (campaign TMCERT, v2 after two design-review rounds: a certificate checker for finite-horizon stateful control
games; trusted-monitoring layer, direction A). Game: Blue's controller folded into rows (catastrophe cat n s a,
continuation K n s a s'); model index theta; row-local admissibility adm n s a theta; nature selects admissible rows per
cell after every history (rectangular). Claims: (S) a horizon-N Bellman supersolution V bounds risk for every randomised
history-dependent Red and every selector admissible below N; (P) risk in [0,1] for lawful rows; (S') finite seeded
mixtures; (Fx) fixed-model certificate; (FxGap) rectangular is strictly more conservative (3/4 vs 1/2); (Obs) observation
lift; (T) single-model tightness: Vstar least certificate, in [0,1], attained by a deterministic time-dependent Markov Red;
(TR) robust tightness for finite model sets; (U) usefulness sub-solution for the same controller; (Q) computable rational
checker (decide +kernel) with soundness bridge (certificate, V >= 0, Lawful at all horizons; guards t, k > 0); (Vx) vertex
certificates certify the convex-hull family; (Abs) deployment through an abstraction: CoveredV (each concrete row's value
against V dominated by an admissible abstract row) => every concrete history-dependent Red bounded; equality coverage is a
special case. Witness: checker on the FxGap tables, consumed bound 3/4 attained, equality and interior-row coverage.
Brute force and two reviewers' exact checks: all conjuncts true. Classical infrastructure (MDP verification theorem,
robust DP, simulation by abstraction).
