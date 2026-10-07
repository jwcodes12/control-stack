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
