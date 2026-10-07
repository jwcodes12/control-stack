QUESTION (campaign UMCERT, v1 after a Reviewer A and a Reviewer B design review: certificate form of the UMPROT/UMSTRAT
bounds). capB r b a = (1 - r + r a if b >= 1 else a) is the value of one attack passing w.p. a. Claims: (R) exact
one-shot reduction for the halting protocol: every colluding pair (finite shared seed, stateless monitor,
history-dependent generator) has risk <= U iff every one-shot pair (fixed bad x attacked in round 1, stateless rule psi)
has survH(E_{M PH} psi) capB(E_{M x} psi) <= U; any valid kappa, any b, N >= 1, U >= 0. (C) sound envelope certificate:
if E_{M x} psi <= env(E_{M PH} psi) for bad x and every rule, and survH(t) capB(min 1 (env t)) <= U on [0,1], then
risk <= U. (E) envelopes from L-domination (L t) and hockey-stick (e^eta t + delta). (G0) survH antitone in the pass
rate for every kappa in [0,1]. (G) monotone grid certificates. (CG)/(SG) end-to-end grid certificates for the halting
and stratified designs. (D) the UMPROT T3 counting bounds (hard and soft slack) satisfy the certificate hypothesis, so
the certificate is never worse. (F) view-blind floor (AOQL at r = 1 or b = 0). (X) exactness at perfect honeypots
(L = 1 forces M x = push M PH). (Xp) exactness for decodable content-only mediators with minimum bad-class honeypot
mass p: worst case = sup_t survH(t) capB(min 1 (t/p)) (the global-slack column of DESIGN §5). (S1) stratified
certificate binCDF(m, s_c, t) capB(t) <= U; (S2) its necessity under exact decoding, every budget. Witness: grid
certificates (m = 12, s_c = 1: 7/100 vs the counting 2/13; soft slack n_h = 100, n_s = 5: 19/1000 vs 5/101; kink
L = 4, r = 9/10, n_h = 30, n_s = 1: 17/100 vs 0.332) and explicit attaining pairs (>= 6833/100000 at the first).
Brute force (numerics/umcert_check.py; reviewers' own scripts): about 10^5 exact-rational instances, 0 violations.
Classical (first-bad-decides, one-shot reduction, acceptance sampling); infrastructure: Lean-checked design tables.
