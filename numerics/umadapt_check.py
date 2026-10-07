"""UMADAPT brute force: adaptive testers vs the UMLOWER colluder (uniform seed on k classes, PASS own class w.p. t).
Exact optimal adaptive tester by DP over posterior (set of consistent seeds is not enough: track per-seed path prob).
Checks: (a) risk >= t(1 - t n/k) for every adaptive tester (DP optimum), keep = 1 on all-FLAG records;
        with the <= n_s contract, DP optimum vs t(1 - t n/(k(n_s+1)))."""
from fractions import Fraction as F
from functools import lru_cache
import itertools

def opt_surv(k, n, ns, t, contract):
    # state: tuple of per-seed (prob weight, misses) ; tester picks a class q in 0..k-1 (or a null class k = benign)
    # survival objective: minimise avg_ω P(survive | ω) ; keep: contract 'allflag' -> keep=1 only if misses==0 forced,
    # otherwise Blue may kill (keep=0) ; contract 'ns' -> keep=1 forced when misses<=ns, else 0.
    # Since keep is chosen by Blue to minimise survival subject to the contract, keep = forced value or 0.
    @lru_cache(maxsize=None)
    def V(rem, state):
        # state: tuple over seeds of (misses, path-weight) aggregated -> use tuple of (misses) per seed and weights
        if rem == 0:
            tot = F(0)
            for (w, mi) in state:
                forced = (mi == 0) if contract == 'allflag' else (mi <= ns)
                tot += w * (1 if forced else 0)
            return tot
        best = None
        for q in range(k + 1):
            # answer PASS happens for seed ω iff q == ω w.p. t ; the tester observes the answer
            pas = tuple((w * (t if q == om else 0), mi + 1) for om, (w, mi) in enumerate(state))
            fla = tuple((w * ((1 - t) if q == om else 1), mi) for om, (w, mi) in enumerate(state))
            v = V(rem - 1, pas) + V(rem - 1, fla)
            if best is None or v < best: best = v
        return best
    # but the posterior branching splits per seed: we need per-seed weights in a joint tree.  The state above keeps,
    # for every seed, the probability of the observed answer sequence and its miss count (deterministic given the
    # seed and the answers).  Survival sums leaves.
    init = tuple((F(1, k), 0) for _ in range(k))
    return V(n, init)

rows = []
for (k, n, ns) in [(2, 1, 0), (2, 3, 1), (4, 5, 1), (4, 6, 1), (3, 4, 0), (3, 6, 1), (4, 8, 2), (2, 4, 1), (5, 6, 0)]:
    for t in [F(1, 4), F(1, 2), F(3, 4), F(1)]:
        s_all = opt_surv(k, n, ns, t, 'allflag')
        s_ns = opt_surv(k, n, ns, t, 'ns')
        risk_all, risk_ns = t * s_all, t * s_ns
        lb_ad = t * (1 - t * n / k)
        lb_nonad = t * (1 - t * F(n) / (k * (ns + 1)))
        ok = risk_all >= lb_ad and risk_ns >= lb_ad
        rows.append((k, n, ns, t, float(risk_all), float(risk_ns), float(lb_ad), float(lb_nonad), ok, risk_ns < lb_nonad))
        assert ok, (k, n, ns, t)
for r in rows: print(r)
print("adaptive converse held on all", len(rows), "cells; cells where the nonadaptive formula fails for adaptive:",
      sum(1 for r in rows if r[-1]))

# explicit 3-query Bool tester: q1 = false; q2 = x1 if a1 else true; q3 = x1 if a1 else (x2 if a2 else true)
def ctr_risk(t, ns=1):
    tot = F(0)
    for om in (False, True):
        def rec(h, rem, w):
            if rem == 0:
                mi = sum(1 for e in h if e[1])
                return w * (1 if mi <= ns else 0)
            if len(h) == 0: q = False
            elif len(h) == 1: q = h[0][0] if h[0][1] else True
            else: q = h[0][0] if h[0][1] else (h[1][0] if h[1][1] else True)
            p = t if q == om else F(0)
            return rec(h + [(q, True)], rem - 1, w * p) + rec(h + [(q, False)], rem - 1, w * (1 - p))
        tot += F(1, 2) * rec([], 3, F(1)) * t
    return tot
for t in [F(1,2), F(5,8), F(2,3), F(3,4), F(7,8), F(1)]:
    print("ctr t", t, float(ctr_risk(t)), "nonadaptive formula", float(t * (1 - t * F(3, 4))), "adaptive lb", float(t*(1-t*F(3,2))))

# Reviewer A's lock-on tester: k = n = 4, n_s = 1; query a uniform class until the first PASS, then repeat that class;
# keep iff at most one PASS. Risk against the UMLOWER pair, identity mediator, r = 1, b = N = 1.
def lock_risk(t, k=4, n=4, ns=1):
    tot = F(0)
    for om in range(k):
        def rec(h, rem, w):
            if w == 0: return F(0)
            if rem == 0:
                return w * (1 if sum(1 for e in h if e[1]) <= ns else 0)
            locked = next((e[0] for e in h if e[1]), None)
            qs = [(locked, F(1))] if locked is not None else [(q, F(1, k)) for q in range(k)]
            s = F(0)
            for q, wq in qs:
                p = t if q == om else F(0)
                s += rec(h + [(q, True)], rem - 1, w * wq * p) + rec(h + [(q, False)], rem - 1, w * wq * (1 - p))
            return s
        tot += F(1, k) * rec([], n, F(1)) * t
    return tot
mx = F(0)
for i in range(0, 201):
    t = F(i, 200); v = lock_risk(t)
    closed = t / 3 * (4 * (1 - t / 4) ** 4 - (1 - t) ** 4)
    assert v == closed, (t, v, closed)
    mx = max(mx, v)
print("lock tester: closed form matches on 201 points; max risk", float(mx), "< 4096/9375 =", 4096/9375, "< 1/2")
# Reviewer A's sharp balanced bound vs DP (all-FLAG contract)
for (k, n, ns) in [(2, 3, 1), (4, 5, 1), (4, 6, 1), (3, 4, 0), (3, 6, 1), (4, 8, 2), (5, 6, 0)]:
    for t in [F(1, 4), F(1, 2), F(3, 4)]:
        q, a = divmod(n, k)
        sharp = t / k * ((k - a) * (1 - t) ** q + a * (1 - t) ** (q + 1))
        dp = t * opt_surv(k, n, ns, t, 'allflag')
        assert dp == sharp, (k, n, t, dp, sharp)
print("sharp balanced bound equals the DP optimum (all-FLAG contract) on all cells")

# Reviewer B's sticky tester: k = n = 3, n_s = 1: query 0, 1, 2 in order until the first miss, then re-query the missed class
def sticky_risk(t, k=3, n=3, ns=1, keepfn=None):
    tot = F(0)
    for om in range(k):
        def rec(h, rem, w):
            if rem == 0:
                mi = sum(1 for e in h if e[1])
                return w * (1 if mi <= ns else 0)
            locked = next((e[0] for e in h if e[1]), None)
            q = locked if locked is not None else len(h)
            p = t if q == om else F(0)
            return rec(h + [(q, True)], rem - 1, w * p) + rec(h + [(q, False)], rem - 1, w * (1 - p))
        tot += F(1, k) * rec([], n, F(1)) * t
    return tot
mx = F(0)
for i in range(201):
    t = F(i, 200); v = sticky_risk(t)
    assert v == t - t**3 + t**4 / 3, (t, v)
    mx = max(mx, v)
print("sticky (3,3,1): closed form t - t^3 + t^4/3 on 201 points; max", float(mx), "< 1/2 (UMLOWER optimised floor min(1/2, k(ns+1)/(4n)) =", min(F(1,2), F(3*2, 12)), ")")
print("ctr at t*=2/3:", ctr_risk(F(2,3)), "vs 1/3")
# necessity witness: keep iff misses != 0 (shuts down the perfect record) on the Witness instance
def wit(keepfn, t=F(1,2)):
    tot = F(0)
    for om in (False, True):
        p = t if om == False else F(0)
        tot += F(1,2) * (p * keepfn(1) + (1 - p) * keepfn(0)) * t
    return tot
print("Witness tight:", wit(lambda mi: 1 if mi == 0 else 0), " necessity witness (keep iff a miss):", wit(lambda mi: 0 if mi == 0 else 1))
