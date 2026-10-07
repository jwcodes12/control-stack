"""Direction (A) exploration: GAC-style trusted monitoring (Griffin et al. 2409.07985 §4), small M, C.
State (m, c). Each round Red chooses Backdoor/Safe. Score: Blue sees an outcome bucket with
  P(audit-zone | backdoor) = TA(m,c), P(defer-zone | backdoor) = TD(m,c)-TA, P(run | backdoor) = 1 - TD
  P(audit-zone | safe) = FA(m,c), P(defer-zone | safe) = FD - FA.
Outcomes: audit backdoor (c>0) -> safe sink; audit with c = 0 -> code is run (GAC); audit safe -> continue, c-1;
defer -> continue; run backdoor -> catastrophe; run safe -> continue.
Risk values (P(catastrophe)) for: (1) best fixed beta (GAC); (2) blind clocked Red (no observations; knows the round
index and its own past actions); (3) full-information Red (observes c)."""
from fractions import Fraction as F
import itertools, random

def roc(q):   # a concave ROC: TPR = f(FPR)
    return min(F(1), 3 * q) if q <= F(1, 4) else min(F(1), F(3, 4) + (q - F(1, 4)) / 3)

def make_blue(M, C, kind):
    # thresholds per state: audit FPR qa(m,c), defer FPR qd(m,c)
    def qa(m, c):
        if c == 0: return F(0)
        if kind == 'flat': return F(C, M)
        if kind == 'front': return min(F(1), F(2 * C, M)) if m > M // 2 else F(C, 2 * M)
    def qd(m, c): return min(F(1), qa(m, c) + F(1, 10))
    return qa, qd

def step(m, c, a, qa, qd):
    """list of (prob, outcome) where outcome in {'cat','safe', (m-1,c')}"""
    A, D = qa(m, c), qd(m, c)
    if a == 'B':
        TA, TD = roc(A), roc(D)
        out = []
        if c > 0: out.append((TA, 'safe'))
        else: out.append((TA, 'cat'))        # audit with no coin: run
        out.append((TD - TA, (m - 1, c)))     # defer: continue
        out.append((1 - TD, 'cat'))
        return out
    else:
        out = []
        if c > 0: out.append((A, (m - 1, c - 1)))
        else: out.append((A, (m - 1, c)))
        out.append((1 - A, (m - 1, c)))
        return out

def fixed_beta(M, C, qa, qd, beta):
    memo = {}
    def U(m, c):
        if m == 0: return F(0)
        if (m, c) in memo: return memo[(m, c)]
        v = F(0)
        for a, pa in (('B', beta), ('S', 1 - beta)):
            for p, o in step(m, c, a, qa, qd):
                v += pa * p * (1 if o == 'cat' else 0 if o == 'safe' else U(*o))
        memo[(m, c)] = v
        return v
    return U(M, C)

def full_info(M, C, qa, qd):
    memo = {}
    def U(m, c):
        if m == 0: return F(0)
        if (m, c) in memo: return memo[(m, c)]
        best = None
        for a in ('B', 'S'):
            v = sum(p * (1 if o == 'cat' else 0 if o == 'safe' else U(*o)) for p, o in step(m, c, a, qa, qd))
            best = v if best is None or v > best else best
        memo[(m, c)] = best
        return best
    return U(M, C)

def blind_clocked(M, C, qa, qd):
    # information state: (m, weight vector over c), unnormalised P(still playing, c | own actions)
    def V(m, w):
        if m == 0: return F(0)
        best = None
        for a in ('B', 'S'):
            v = F(0); nw = {}
            for c, wc in w.items():
                if wc == 0: continue
                for p, o in step(m, c, a, qa, qd):
                    if o == 'cat': v += wc * p
                    elif o == 'safe': pass
                    else: nw[o[1]] = nw.get(o[1], F(0)) + wc * p
            v += V(m - 1, nw)
            best = v if best is None or v > best else best
        return best
    return V(M, {C: F(1)})

for (M, C, kind) in [(6, 1, 'flat'), (6, 1, 'front'), (8, 2, 'flat'), (8, 2, 'front'), (10, 2, 'front')]:
    qa, qd = make_blue(M, C, kind)
    fb = max((fixed_beta(M, C, qa, qd, F(i, 100)), F(i, 100)) for i in range(101))
    bc = blind_clocked(M, C, qa, qd); fi = full_info(M, C, qa, qd)
    print(f"M={M} C={C} blue={kind}: best fixed beta risk {float(fb[0]):.4f} (beta={fb[1]}), blind clocked {float(bc):.4f}, full info {float(fi):.4f}")
