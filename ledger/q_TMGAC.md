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
QUESTION (campaign TMGAC, v1 after a design review: Games for AI Control, arXiv 2409.07985 v2, trusted monitoring with a
perfect auditor, as an instance of PL_TMCERTF1). gac: state = coins c; zones TA (backdoor audit), TD (backdoor
audit-or-defer), FA (safe audit); audit with a coin catches; with no coin runs; defer continues. gacQ: ROC f, FPRs qa <= qd,
index m = n + 1; c = 0 convention qa m 0 = 0, f 0 = 0. Claims: (L) lawful; (LQ) adapter lawful for valid thresholds and
monotone ROC; (Z) 1 - risk(constRed beta) = zGAC (App. C.1 case analysis; algebraic identity); (UZ) honest used-solution
reward 1 - qd + [c>0] qa gives uGAC (App. C.2: run or audited-and-safe count, deferred does not); (M) finite mixtures of
constant rates; (Lip) |risk(b) - risk(b')| <= N|b - b'|; (Grid) grid j/J bounds every rate up to N/(2J); (W) at C = 0 always
backdooring attains Vstar; (T5) three problems, one coin: constant rates <= 13/50 (equality at 4/5); a round-index-only Red
11/32 = Vstar; a coin-count-only Red 9/32. Witness: exG3 = gacQ (genuine ROC), certificate exV3 consumed (every Red <= 11/32),
usefulness 19/8; adapter instance safety 63/64, usefulness 3/2; audited-only usefulness 1. Exact numerics: 2400 bridge
comparisons with monotone ROC tables and unrestricted algebra, 0 mismatches. A sensitivity result against GAC's explicit
null-observation assumption, not a refutation.
