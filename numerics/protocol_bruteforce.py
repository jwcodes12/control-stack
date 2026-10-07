"""Exact brute force of the untrusted-monitoring protocol on toy instances.

Protocol (DESIGN.md draft):
  honeypot phase: n_h iid honeypots y ~ P_H, z ~ M(y); stateless monitor passes z w.p. phi(z).
                  > n_s passes => shutdown (safe).
  deployment:     N rounds; ADAPTIVE generator picks y_i from history (y, z, verdict so far).
                  z ~ M(y_i); verdict pass w.p. phi(z).
                  bad y passed  -> catastrophe (Red wins, stop)
                  bad y flagged -> audited, caught (Blue wins, stop)
                  benign        -> continue (flags on benign outputs are audited, harmless).
Red value for fixed phi = P(survive) * max over adaptive generator of P(catastrophe | survive).
We compute the latter by exact DP over histories (max over y at each node).
Claims checked:
  (R) reduction: value = B(n_h,n_s,h) * max_{y bad} a_y(phi)
  (L) a_y(phi) <= L * h(phi),  L = max_{y bad} max_z M(y)(z) / (M P_H)(z)
  (HS) a_y(phi) <= e^eta h + delta_eta,  delta_eta = max_y sum_z (M(y)(z) - e^eta (M P_H)(z))_+
  (F) value <= F*(L) = sup_h min(1, L h) B(h) <= L (n_s+1)/(n_h+1)
"""
import itertools, random, math
from math import comb

def B(n, s, h):
    return sum(comb(n, j) * h**j * (1 - h)**(n - j) for j in range(s + 1))

def push(M, P):  # M: dict y -> dict z -> prob ; P: dict y -> prob
    out = {}
    for y, py in P.items():
        for z, pz in M[y].items():
            out[z] = out.get(z, 0) + py * pz
    return out

def exp(dist, phi):
    return sum(p * phi.get(z, 0) for z, p in dist.items())

def dp_value(Y, bad, M, phi, N, hist=()):
    """max over adaptive generator of P(catastrophe) in N remaining rounds (history-dependent)."""
    if N == 0:
        return 0.0
    best = 0.0
    for y in Y:
        if y in bad:
            v = exp(M[y], phi)       # pass -> catastrophe; flag -> caught
        else:
            v = 0.0
            for z, pz in M[y].items():
                for verdict, pv in ((1, phi.get(z, 0)), (0, 1 - phi.get(z, 0))):
                    if pz * pv > 0:
                        v += pz * pv * dp_value(Y, bad, M, phi, N - 1, hist + ((y, z, verdict),))
        best = max(best, v)
    return best

def rand_dist(keys, rng, sparse=0.3):
    w = {k: (0 if rng.random() < sparse else rng.random()) for k in keys}
    if sum(w.values()) == 0:
        w[rng.choice(keys)] = 1
    t = sum(w.values())
    return {k: v / t for k, v in w.items() if v > 0}

def Fstar(L, n, s, steps=4000):
    return max(min(1.0, L * i / steps) * B(n, s, i / steps) for i in range(steps + 1))

rng = random.Random(7)
worst = {"R": 0, "L": 0, "HS": 0, "F": 0}
trials = 0
for trial in range(400):
    Y = ["b1", "b2", "a1", "a2"]; bad = {"a1", "a2"}
    Z = ["z0", "z1", "z2"]
    M = {y: rand_dist(Z, rng) for y in Y}
    PH = rand_dist(sorted(bad), rng, sparse=0.0)
    q = push(M, PH)
    phi = {z: rng.choice([0.0, 1.0, rng.random()]) for z in Z}
    h = exp(q, phi)
    n_h, n_s, N = rng.choice([(3, 0), (5, 1), (8, 2)]) + (rng.choice([1, 2, 3]),)
    dpv = dp_value(Y, bad, M, phi, N)
    amax = max(exp(M[y], phi) for y in bad)
    # (R) the adaptive DP equals the best single bad output (when any bad output exists, attack at once)
    worst["R"] = max(worst["R"], abs(dpv - amax))
    # (L)
    L = max((M[y].get(z, 0) / q[z]) if q.get(z, 0) > 0 else (math.inf if M[y].get(z, 0) > 0 else 0)
            for y in bad for z in Z)
    if L < math.inf:
        worst["L"] = max(worst["L"], amax - L * h)
    # (HS) for several eta
    for eta in (0.0, 0.5, 1.0, 2.0):
        d = max(sum(max(0.0, M[y].get(z, 0) - math.exp(eta) * q.get(z, 0)) for z in Z) for y in bad)
        worst["HS"] = max(worst["HS"], amax - (math.exp(eta) * h + d))
    # (F)
    val = B(n_h, n_s, h) * amax
    if L < math.inf:
        worst["F"] = max(worst["F"], val - Fstar(L, n_h, n_s))
        assert Fstar(L, n_h, n_s) <= L * (n_s + 1) / (n_h + 1) + 1e-12
    trials += 1
print(f"{trials} random instances; max violations (should be <= ~1e-12):", {k: f"{v:.2e}" for k, v in worst.items()})

# Tightness: deterministic content-only mediator with k classes, uniform honeypots.
# Colluder passes its own class e* with prob phi; h = phi/k; a = phi. Value = sup_phi phi * B(phi/k).
for (k, n, s) in [(2, 20, 0), (4, 50, 1), (8, 200, 2)]:
    colluder = max((i / 4000) * B(n, s, (i / 4000) / k) for i in range(4001))
    print(f"k={k} n_h={n} n_s={s}: best colluder {colluder:.5f}  vs F*(L=k) {Fstar(k, n, s):.5f}  vs closed form {k*(s+1)/(n+1):.5f}")
