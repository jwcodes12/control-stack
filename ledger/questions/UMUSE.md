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
