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
QUESTION (campaign UMUSE: the usefulness companion, v2 after the Reviewer A and Reviewer B design reviews). In the halting
protocol of UMPROTF1, a monitor that FLAGs everything satisfies every safety upper bound, so the bounds measure only
the adversarial gain over always-flag. This campaign puts the HONEST side of the same recursions in Lean and adds a
usefulness-constrained obstruction:
(a) the false halt of an iid benign submission stream is P(Bin(N, f0) > b); 1 - haltP is the survival recursion with
    the audit budget as hard slack;
(b) honest completion (test survival times no false halt) = survH(alpha0) * binCDF(N, b, f0) for every valid shutdown
    schedule; (b') the class-aware product of per-class CDFs;
(c') exact risk of the view-blind pair (pass w.p. h, submit one fixed bad x), b = 0 included, with no honeypot-support
    hypothesis;
(P) the identity D * risk(view-blind at alpha0) = q * completion, hence for every universal risk certificate X and
    every completion target u: q u <= D X and alpha0 u <= X;
(d), (d') hypothesis-free Cantelli inequalities for both binomial tails (slack cost and sufficient slack);
(f) the honest ROC constraint 1 - f0 <= e^eta alpha0 + hs_eta(M mu, M PH) (from UMHS T2): mediation can only hurt the
    honest monitor;
(g) at b = 0 the domination bound sharpens to L (n_s+1)/(n_h+1) (no 1 - r term).
The honest half is conditional on a measured honest profile (alpha0, f0, mu) and is NOT capability-free; honest
completion is full-run availability, not task usefulness. Brute force: numerics/umuse_frontier.py; both design reviewers
checked (a), (b), (c'), (d), (d') and (f) in exact arithmetic on hundreds to thousands of instances with 0 violations.
