QUESTION (campaign UMSTRAT: stratified honeypots, class-aware shutdown). Content-only mediator (view law K (c x)); m
honeypots per bad class; shut down if any class has > s_c misses. Claim: every colluding pair has P(uncaught
catastrophe) <= (1-r) + r (s_c+1)/(m+1) (no factor for the number of classes), and with decodable classes an explicit
colluder attains binCDF m s_c t * (1 - r + r t) for every t in [0,1]. Numerics: numerics/realistic_budgets.py shows the
stratified design beats a global iid counter when the honest monitor misses honeypots (e.g. n_h=100, alpha0=5%, k=8:
0.163 vs 0.415).
