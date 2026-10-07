"""DESIGN v1 section 5: realistic honeypot budgets (n_h <= 100; Greenblatt 30, LASR <= 100 shared with audits).
Global iid honeypots + global hard slack n_s  vs  stratified (m = n_h/k per class) + class-aware slack s_c.
Slack is the smallest value keeping the honest monitor's false-shutdown probability <= 10% (honest miss rate a0).
Values are exact sups over a fine grid (r = 1, delta = 0, content-only decodable classes: L = k for global iid)."""
from math import comb
def F(n, s, h): return sum(comb(n, j) * h**j * (1 - h)**(n - j) for j in range(min(s, n) + 1))
def grid_sup(f, steps=4000): return max(f(i / steps) for i in range(steps + 1))
def min_slack(n, a0, budget, classes=1):
    for s in range(n + 1):
        if 1 - F(n, s, a0) ** classes <= budget: return s
    return n
print(f"{'n_h':>4} {'a0':>5} {'k':>3} | {'global n_s':>10} {'X_global':>9} | {'m':>3} {'s_c':>3} {'X_strat':>8}")
for nh in (30, 100):
    for a0 in (0.0, 0.01, 0.05):
        for k in (1, 2, 4, 8, 16):
            ns = min_slack(nh, a0, 0.10)
            Xg = grid_sup(lambda h: min(1, k * h) * F(nh, ns, h))
            m = nh // k
            if m == 0: continue
            sc = min_slack(m, a0, 0.10, classes=k)
            Xs = grid_sup(lambda h: h * F(m, sc, h))
            print(f"{nh:4d} {a0:5.2f} {k:3d} | {ns:10d} {Xg:9.3f} | {m:3d} {sc:3d} {Xs:8.3f}")
# general kill schedule lemma: sup_h h S_kappa(h) <= (sum_{j<=n} prod_{i<j}(1-kappa_i))/(n+1)
import random
rng = random.Random(1); worst = 0
def S(h, kap, n, j=0):
    if n == 0: return 1.0
    return (1 - h) * S(h, kap, n - 1, j) + h * (1 - kap[j]) * S(h, kap, n - 1, j + 1)
for _ in range(400):
    n = rng.randint(0, 7); kap = [rng.choice([0, 1, rng.random()]) for _ in range(n + 1)]
    bound = sum(__import__("math").prod(1 - kap[i] for i in range(j)) for j in range(n + 1)) / (n + 1)
    worst = max(worst, grid_sup(lambda h: h * S(h, kap, n), 400) / bound)
print(f"general kill-schedule lemma: max sup/bound over 400 random schedules = {worst:.4f} (<= 1 required)")
