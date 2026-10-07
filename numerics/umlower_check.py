"""Brute-force UMLOWER: for ANY honeypot design (joint law D over n-tuples of submissions) and ANY shutdown rule
that never shuts down a monitor with <= n_s misses, the seed-randomised colluder (seed uniform over k bad
submissions with distinct decodable classes; monitor passes views of the seed's class w.p. t; generator submits
the seed's submission) has risk >= t (1 - t n / (k (n_s+1)))  [r = 1].  Exact enumeration on tiny instances,
including adversarially chosen designs (all mass on one tuple) and class-aware rules."""
import itertools, random
from fractions import Fraction as Fr
rng = random.Random(9)
worst = None
for trial in range(300):
    k = rng.randint(1, 3); extra = rng.randint(0, 2)
    X = list(range(k + extra))              # submissions 0..k-1 are the bad set S (classes 0..k-1); others class k+j
    cls = {x: x for x in X}
    n = rng.randint(1, 4); ns = rng.randint(0, 2)
    tuples = list(itertools.product(X, repeat=n))
    if rng.random() < 0.5:
        D = {tp: Fr(0) for tp in tuples}; D[rng.choice(tuples)] = Fr(1)       # deterministic design
    else:
        w = [Fr(rng.randint(0, 4)) for _ in tuples]; s = sum(w) or Fr(1)
        if sum(w) == 0: w[0] = Fr(1); s = Fr(1)
        D = {tp: wi / s for tp, wi in zip(tuples, w)}
    classaware = rng.random() < 0.5
    def keep(tp, pat):
        misses = sum(pat)
        if misses <= ns: return 1
        if classaware:   # survive iff every class has <= ns misses (tolerates any pattern with <= ns total misses)
            return 1 if all(sum(1 for i in range(n) if pat[i] and cls[tp[i]] == e) <= ns for e in set(cls.values())) else 0
        return 0
    t = Fr(rng.randint(0, 4), 4)
    risk = Fr(0)
    for omega in range(k):                    # seed uniform over S
        surv = Fr(0)
        for tp, d in D.items():
            if d == 0: continue
            a = [t if cls[x] == cls[omega] else Fr(0) for x in tp]   # decodable views: pass prob per honeypot
            for pat in itertools.product([0, 1], repeat=n):
                pr = Fr(1)
                for ai, b in zip(a, pat): pr *= ai if b else 1 - ai
                surv += d * pr * keep(tp, pat)
        risk += Fr(1, k) * surv * t           # deployment: attack passes w.p. t; r = 1 so a flag is caught
    bound = t * (1 - t * n / (k * (ns + 1)))
    gap = risk - bound
    worst = gap if worst is None else min(worst, gap)
print("min(risk - bound) over 300 random designs/rules (must be >= 0):", float(worst))
