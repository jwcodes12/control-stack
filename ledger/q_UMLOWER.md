PROGRAMME CONTEXT. We are building a Lean-verified, CAPABILITY-FREE guarantee stack for AI control (Redwood/GDM-style
untrusted monitoring): theorems of the form "for every policy the untrusted model could follow, P(uncaught catastrophe)
<= X" with X a function of explicit parameters of trusted components (mediator kernel M, honeypot law P_H, shutdown
schedule, n_h, audit recall r, catastrophe set Bad). Design document (hostile-reviewed by Reviewer A and
Reviewer B; all core inequalities judged true; v1 incorporates every fix): DESIGN.md.
Model in one paragraph: submissions x in a finite X; a trusted mediator kernel M : X -> Z -> R gives the monitor's whole
view z; the untrusted monitor is a stateless rule phi : Z -> [0,1] (prob. of PASS) depending on a shared seed omega with
the generator; the generator is any history-dependent randomised policy; an upfront test runs n_h iid honeypots from
P_H (a PASS on a honeypot is a miss; the (j+1)-th miss shuts down with prob. kappa_j); then N deployment rounds: PASS on
a bad submission = catastrophe; FLAG uses an audit while u < b (bad caught w.p. r, else executes), FLAG with no audit
left halts (safe).

PROGRAMME OWNER'S OVERRIDE: classical lemmas are WELCOME as infrastructure for the stack. Triviality alone is
NOT a reason to kill these formulations; report novelty honestly in "trivial_tool"/"known_refs" but judge the verdict
on FIDELITY (does the Lean say what the informal claim says, with no excess or missing binders, no wrong-reason truth),
VACUITY (are the hypotheses jointly satisfiable non-trivially; is the Witness meaningful) and FALSITY (is any conjunct
false? try counterexamples, edge cases: empty Bad, zero entries, h=0, n_s >= n_h, r in {0,1}, b=0, N=0, eta<0).
QUESTION (campaign UMLOWER: a design-free converse). For a mediator with an exact decoder for a content class and k
>= 1 bad submissions with distinct classes, for ANY honeypot design (an arbitrary joint law over n-tuples of
submissions, independent of the colluders' seed) and ANY shutdown rule that never shuts down a monitor with <= n_s
misses (global or class-aware slack are special cases), and every audit recall r in [0,1] and t in [0,1], a
seed-randomised colluding pair (seed uniform on the k submissions; the monitor passes the seed's class w.p. t; the
generator submits the seed's submission) has P(survive test, then uncaught catastrophe) >= t (1 - t n /(k (n_s+1))).
Proof idea: averaged over the seed, expected misses <= t n / k; Markov. With the stratified upper bound (UMSTRATF1),
honeypot budget per distinguishable class is necessary and sufficient: risk = Theta(k (n_s+1)/n). Brute force: exact
enumeration over 300 random designs (incl. deterministic and class-aware rules): min(risk - bound) = 0
(numerics/umlower_check.py); the bound is attained in the Witness instance (risk = 1/4).
