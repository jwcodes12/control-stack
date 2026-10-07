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
QUESTION (campaign UMHS: testing infrastructure). State, as Lean infrastructure on finite real-valued laws:
T2 hockey-stick pass bound E_P phi <= e^eta E_Q phi + hs_eta(P||Q) for every [0,1]-valued rule and every real eta, with
attainment; T1 (advantage <= TV); T4a kernel data processing for hs; T4b content-factorisation upper bound; T4c floor
for content-preserving mediators (exact decoder) and its approximate-decoder version with constant (1+e^eta) gamma; T5d
perturbation lemma; T4c' maximal-leakage floor (no law Q gives a likelihood-ratio constant below sum_z max_{x in B} M x z;
attained); domination from class coverage. Brute force: 3000 random instances, no violations of T2/T4b/T4c/T5d
(numerics/floor_minimax.py); Reviewer B independently: 2000 random mediators, max-leakage floor 0 violations.
