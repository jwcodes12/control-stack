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
QUESTION (campaign UMPROT: protocol safety). For the protocol recursion `cat`/`protocolCat` (definitions in the
statement; honeypot survival from UMSURV): (T3a) first bad submission decides, budget-sensitive: if every bad
submission's attack pass probability is <= A then for every history and adaptive generator, cat <= 1 - r + rA while an
audit is available and <= A otherwise; (T3*) a generator that submits a fixed bad x at once attains
surv * (1 - r + r E_{M x} phi); (T3) closed forms: domination form (1-r) + r L (n_s+1)/(n_h+1), hockey-stick form
(1-r) + r(delta + e^eta (n_s+1)/(n_h+1)), soft form (1-r) + r L n_s/(n_h+1). Brute force: exact DP over adaptive
generators equals the formula to 4e-16 on 300 instances with budget, recall and halting
(numerics/simulate_protocol.py; Reviewer B's independent exact-Fraction DP: 0 mismatches); the recurrence equals an
independent sampling simulation of the operational protocol within Monte Carlo error.
