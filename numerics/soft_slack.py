"""Soft (LASR-style) slack: each honeypot PASS independently 'kills' (retrains/shuts down) the
colluding monitor with probability kappa (LASR: kappa = 1/n_s).  Survival S(h) = (1 - kappa h)^{n_h}
(exact binomial thinning; LASR's exp(-n_h h/n_s) is its Poisson limit).
Claims:  (a) the recursion with a general kill schedule reproduces both survival laws;
         (b) h * (1 - kappa h)^n <= 1/(kappa (n+1))   for h in [0,1], kappa in (0,1].
"""
from math import comb
from fractions import Fraction as Fr

def surv_rec(n, h, kill, j=0):
    # P(survive n honeypots) when each honeypot is passed w.p. h and the (j+1)-th pass kills w.p. kill(j)
    if n == 0:
        return 1
    return (1 - h) * surv_rec(n - 1, h, kill, j) + h * (1 - kill(j)) * surv_rec(n - 1, h, kill, j + 1)

def B(n, s, h):
    return sum(comb(n, j) * h**j * (1 - h)**(n - j) for j in range(s + 1))

for n in range(0, 9):
    for s in range(0, 4):
        for h in (Fr(1, 3), Fr(3, 4)):
            assert surv_rec(n, h, lambda j: 1 if j >= s else 0) == B(n, s, h)          # hard slack
            for kap in (Fr(1, 2), Fr(1, 5)):
                assert surv_rec(n, h, lambda j: kap) == (1 - kap * h) ** n             # soft slack
print("(a) recursion = binomial CDF (hard) and (1-kappa h)^n (soft): exact on n<=8")

worst = 0
for n in range(0, 60):
    for kap in [1, 0.5, 0.2, 0.1, 0.05]:
        best = max((i / 5000) * (1 - kap * i / 5000) ** n for i in range(5001))
        worst = max(worst, best * kap * (n + 1))
print(f"(b) max of h(1-kappa h)^n * kappa(n+1) over grid = {worst:.4f} (<= 1 required)")
# LASR parameters: n_h <= 100 (budget 2% of N=5000 shared with audits), n_s = 5
for L in (1, 2, 8):
    v = max(min(1, L * i / 100000) * (1 - (i / 100000) / 5) ** 100 for i in range(100001))
    print(f"LASR params n_h=100, n_s=5, L={L}: soft-slack F* = {v:.4f}; closed form L n_s/(n_h+1) = {L*5/101:.4f}")
