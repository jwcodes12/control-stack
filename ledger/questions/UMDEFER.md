QUESTION (campaign UMDEFER, v2 after the Reviewer A design review: audit-then-defer-after-exhaustion). The halting
protocol of UMPROTF1 while audits remain; a FLAG with no audit left halts w.p. eta, else DEFERS (trusted
replacement; continue at the same u); a deferred bad submission ends safely w.p. alpha (a uniform conditional
floor, e.g. fresh-coin audits of a q fraction with recall r give alpha = q r; a separately funded service; NOT an
average rate). theta = eta + (1 - eta) alpha. Claims: (a) eta = 1 recovers cat/protocolCat; 0 <= catD <= 1;
(b) finite state bound catD <= finiteCap r A theta b n u (decide at once while audits remain, or burn b - u audits
then retry n - (b - u) times), every theta in [0,1]; (c) attainment retry A theta n at an exhausted budget, its
division-free closed form and the ratio A/(theta + A(1 - theta)); (d) a protocol certificate: if
survH t (hardKill n_s) n_h 0 * finiteCap(min 1 (L t)) <= U for all t in [0,1] then every colluding pair has risk <= U,
and the coarse corollary max([0<b]((1-r) + rH), H/theta), H = L(n_s+1)/(n_h+1); (e) no-go without a stopping hazard
(eta = alpha = 0) for EVERY Bool honeypot law and every horizon: exact risk binCDF(n_h, n_s, PH(true) t)(1-(1-t)^(N-b))
of a burn-then-attack colluder, >= (1-t)^n_h (1-(1-t)^(N-b)); (e') along t_K = 1/sqrt(K+1) that lower bound tends to 1.
Scope: free-submission model without a benign-flag guard (Greenblatt et al. App. G and LASR inverse honeypots are
guards); not a necessity theorem for incrimination; not a model of Ctrl-Z resampling. Prior art for the per-attempt
ratio: Shlegeris, "Win/continue/lose scenarios and execute/replace/audit protocols" (Redwood blog, Nov 2024); LASR
u/(c+u). Brute force: numerics/umdefer_check.py and numerics/umdefer_v2_check.py (exact; 0 violations).
