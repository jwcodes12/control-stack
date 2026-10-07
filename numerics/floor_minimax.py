"""Brute-force T4b/T4c/T5b/T5d on random toy instances.

Setup: X = submissions with content c(x) in C; Bad subset X; honeypot law PH on Bad.
  hs(eta,P,Q) = sum_z max(0, P z - e^eta Q z)
T4c floor   : M content-preserving (decoder g, g(z)=c(x) on supp M x)  =>
              hs(eta, M x, M PH) >= max(0, 1 - e^eta PH(c = c x))       for every x
T4b attain  : M content-only (M x = K(c x))  =>  hs(eta, M x, M PH) <= max(0, 1 - e^eta PH(c = c x))
              and pointwise ratio  M x z / (M PH) z <= 1 / PH(c = c x)
T5b lower   : M content-preserving (NOT necessarily content-only); colluder phi = t * 1{g z = e*}
              with e* = argmin_{e in c(Bad)} PH(c=e), p = PH(c=e*): honeypot pass rate = t p,
              attack pass rate (any bad x with c x = e*) = t.
T5d         : if TV(M x, K(c x)) <= gamma for all x, then hs(eta, M x, M PH) <= hs(eta, K c x, K c# PH) + (1+e^eta) gamma
"""
import random, math
rng = random.Random(11)

def hs(eta, P, Q):
    return sum(max(0.0, P.get(z, 0) - math.exp(eta) * Q.get(z, 0)) for z in set(P) | set(Q))
def tv(P, Q):
    return 0.5 * sum(abs(P.get(z, 0) - Q.get(z, 0)) for z in set(P) | set(Q))
def push(M, P):
    out = {}
    for x, px in P.items():
        for z, pz in M[x].items():
            out[z] = out.get(z, 0) + px * pz
    return out
def rdist(keys, sparse=0.3):
    w = {k: (0 if rng.random() < sparse else rng.random()) for k in keys}
    if sum(w.values()) == 0: w[rng.choice(keys)] = 1
    t = sum(w.values()); return {k: v / t for k, v in w.items() if v > 0}

viol = {"T4c": 0.0, "T4b": 0.0, "T4b_ratio": 0.0, "T5b": 0.0, "T5d": 0.0}
for trial in range(3000):
    C = ["c0", "c1", "c2"]
    X = [f"x{i}" for i in range(6)]
    c = {x: rng.choice(C) for x in X}
    Bad = set(rng.sample(X, rng.randint(1, 5)))
    PH = rdist(sorted(Bad), sparse=0.2)
    eta = rng.choice([0.0, 0.3, 1.0])
    # content-preserving randomised M: each x gets its own law on views tagged with its content
    Mcp = {x: {(c[x], v): p for v, p in rdist(["v0", "v1", "v2"]).items()} for x in X}
    q = push(Mcp, PH)
    pc = {e: sum(PH.get(x, 0) for x in X if c[x] == e) for e in C}
    for x in Bad:
        floor = max(0.0, 1 - math.exp(eta) * pc[c[x]])
        viol["T4c"] = max(viol["T4c"], floor - hs(eta, Mcp[x], q))
    # T5b colluder on the content-preserving M
    badC = sorted({c[x] for x in Bad}); estar = min(badC, key=lambda e: pc[e]); p = pc[estar]
    t = rng.random()
    phi = lambda z: t if z[0] == estar else 0.0
    h = sum(pz * phi(z) for z, pz in q.items())
    viol["T5b"] = max(viol["T5b"], abs(h - t * p))
    for x in Bad:
        if c[x] == estar:
            a = sum(pz * phi(z) for z, pz in Mcp[x].items())
            viol["T5b"] = max(viol["T5b"], abs(a - t))
    # content-only M = K o c with randomised K (supports may overlap)
    K = {e: rdist(["z0", "z1", "z2", "z3"]) for e in C}
    Mco = {x: K[c[x]] for x in X}
    q2 = push(Mco, PH)
    for x in Bad:
        bound = max(0.0, 1 - math.exp(eta) * pc[c[x]])
        viol["T4b"] = max(viol["T4b"], hs(eta, Mco[x], q2) - bound)
        if pc[c[x]] > 0:
            r = max(Mco[x][z] / q2[z] for z in Mco[x] if Mco[x][z] > 0)
            viol["T4b_ratio"] = max(viol["T4b_ratio"], r - 1 / pc[c[x]])
    # T5d: leaky mediator M' close to K o c
    gam_max = 0
    Mleak = {}
    for x in X:
        mix = rng.random() * 0.3
        noise = rdist(["z0", "z1", "z2", "z3"])
        Mleak[x] = {z: (1 - mix) * K[c[x]].get(z, 0) + mix * noise.get(z, 0) for z in ["z0", "z1", "z2", "z3"]}
        gam_max = max(gam_max, tv(Mleak[x], K[c[x]]))
    q3 = push(Mleak, PH)
    for x in Bad:
        lhs = hs(eta, Mleak[x], q3)
        rhs = hs(eta, K[c[x]], q2) + (1 + math.exp(eta)) * gam_max
        viol["T5d"] = max(viol["T5d"], lhs - rhs)
print("max violations over 3000 random instances (<= ~1e-12 means no counterexample):")
for k, v in viol.items():
    print(f"  {k:10s} {v:.3e}")
