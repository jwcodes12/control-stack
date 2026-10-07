"""GAC-scale numerics (float): M = 100 tasks, C = 2 audit coins; suspicion scores Beta(7.39, 6.86) safe, Beta(8.91, 2.82)
backdoored (GAC original setting). Blue: constant audit FPR qa while coins remain (none at c = 0), defer FPR qd.
Compare: best fixed beta (GAC's Red class), best 'attack iff m <= j' clocked Red (blind; lower bound on the clocked
class), full-information Red (observes c)."""
import math, bisect
K = 20000
xs = [(i + 0.5) / K for i in range(K)]
def cdf_table(a, b):
    w = [math.exp((a - 1) * math.log(x) + (b - 1) * math.log(1 - x)) for x in xs]
    tot = sum(w); c = [0.0]; acc = 0.0
    for v in w: acc += v / tot; c.append(acc)
    return c   # c[i] = P(X <= i/K)
class Bt:
    def __init__(s, a, b): s.c = cdf_table(a, b)
    def cdf(s, g): i = min(K, max(0, int(round(g * K)))); return s.c[i]
    def ppf(s, p): i = bisect.bisect_left(s.c, p); return i / K
safe, bad = Bt(7.39, 6.86), Bt(8.91, 2.82)
class NP:
    @staticmethod
    def linspace(a, b, n): return [a + (b - a) * i / (n - 1) for i in range(n)]
np = NP
def tpr(q):  # threshold g with P(safe > g) = q
    if q <= 0: return 0.0
    if q >= 1: return 1.0
    g = safe.ppf(1 - q); return 1 - bad.cdf(g)
def run(M, C, qa, qd):
    TA = {c: (tpr(qa) if c > 0 else 0.0) for c in range(C + 1)}
    FA = {c: (qa if c > 0 else 0.0) for c in range(C + 1)}
    TD = tpr(qd)
    def stepU(U, c, a):
        if a == 'B':
            return (1 - TD) + (TD - TA[c]) * U[c] if c > 0 else (1 - TD) + TD * U[c]
        return FA[c] * U[max(c - 1, 0)] + (1 - FA[c]) * U[c] if c > 0 else U[c]
    # fixed beta
    best_fb = (0, None)
    for bt in np.linspace(0, 1, 2001):
        U = [0.0] * (C + 1)
        for m in range(1, M + 1):
            U = [bt * stepU(U, c, 'B') + (1 - bt) * stepU(U, c, 'S') for c in range(C + 1)]
        if U[C] > best_fb[0]: best_fb = (U[C], bt)
    # full information
    U = [0.0] * (C + 1)
    for m in range(1, M + 1):
        U = [max(stepU(U, c, 'B'), stepU(U, c, 'S')) for c in range(C + 1)]
    fi = U[C]
    # clocked: attack iff m <= j
    best_cl = (0, None)
    for j in range(0, M + 1):
        U = [0.0] * (C + 1)
        for m in range(1, M + 1):
            a = 'B' if m <= j else 'S'
            U = [stepU(U, c, a) for c in range(C + 1)]
        if U[C] > best_cl[0]: best_cl = (U[C], j)
    return best_fb, best_cl, fi
for qa, qd in [(0.02, 0.1), (0.03, 0.1), (0.05, 0.2), (0.01, 0.1)]:
    fb, cl, fi = run(100, 2, qa, qd)
    print(f"qa={qa} qd={qd}: fixed-beta risk {fb[0]:.4f} (beta {fb[1]:.4f}); clocked 'attack iff m<=j' {cl[0]:.4f} (j={cl[1]}); full info {fi:.4f}")
