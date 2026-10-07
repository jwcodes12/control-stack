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
QUESTION (campaign UMADAPT, v1 after a Reviewer A and a Reviewer B design review: a converse for ADAPTIVE honeypot testers).
PL_UMLOWERF1 lower-bounds the risk of NONADAPTIVE joint test designs by t(1 - t n/(k(n_s+1))) for one explicit colluding
pair (uniform seed on k bad submissions in distinct decodable classes; the monitor PASSes the decoded seed class w.p. t;
the generator submits the seed). Adaptive tester: the next honeypot law T h depends on the full test history (honeypots,
views, answers); a final randomised keep h in [0,1]. Contract AcceptsAllFlag: in the reference experiment where the
monitor FLAGs everything (phi = 0) the tester proceeds w.p. 1. Claims: (s) keep = 1 on all-FLAG histories suffices;
(a) for every lawful contract-compliant adaptive tester, every n, t in [0,1], r in [0,1], b, N >= 1:
risk >= t max(0, 1 - t n/k) (identical-until-bad against the reference experiment); (a') at t = min(1, k/(2n)), n >= 1:
risk >= min(1/2, k/(4n)); (c1) an explicit adaptive 2-class tester (n = 3, n_s = 1) makes the PL_UMLOWERF1 formula fail
pointwise (141/512 < 21/64 at t = 3/4; 26/81 < 1/3 at the corollary's t = 2/3); (c2) an explicit 3-class sticky tester
(n = 3, n_s = 1) has risk exactly t - t^3 + t^4/3 < 1/2 for every t, below PL_UMLOWERF1's optimised nonadaptive value 1/2.
Witness: tightness 3/8 at a small instance; a tester that rejects the perfect record violates the contract (risk 1/8).
Brute force (numerics/umadapt_check.py; reviewers' scripts): DP-optimal adaptive testers on > 3000 cells and 600 random
literal-semantics instances, 0 violations; closed forms of (c1), (c2) checked exactly. Classical technique (Shoup's
difference lemma; hard-distribution method); infrastructure for the stack.
