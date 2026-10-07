QUESTION (campaign UMLOWER: a design-free converse). For a mediator with an exact decoder for a content class and k
>= 1 bad submissions with distinct classes, for ANY honeypot design (an arbitrary joint law over n-tuples of
submissions, independent of the colluders' seed) and ANY shutdown rule that never shuts down a monitor with <= n_s
misses (global or class-aware slack are special cases), and every audit recall r in [0,1] and t in [0,1], a
seed-randomised colluding pair (seed uniform on the k submissions; the monitor passes the seed's class w.p. t; the
generator submits the seed's submission) has P(survive test, then uncaught catastrophe) >= t (1 - t n /(k (n_s+1))).
Proof idea: averaged over the seed, expected misses <= t n / k; Markov. With the stratified upper bound (UMSTRATF1),
honeypot budget per distinguishable class is necessary and sufficient: risk = Theta(k (n_s+1)/n). Brute force: exact
enumeration over 300 random designs (incl. deterministic and class-aware rules): min(risk - bound) = 0
(numerics/umlower_check.py); the bound is attained in the Witness instance (risk = 1/4).
