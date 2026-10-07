"""Fidelity check: the recurrences surv/cat are the event probabilities of the protocol as
operationally described (sampling simulation written independently of the recursion), with an
explicit TRUSTED TASK STREAM (tasks t ~ mu iid; generator chooses the output y given t and history).
Also checks Reviewer A's exact deployment value: max over adaptive generators of P(cat) =
   1 - r + r*A  (b > 0),   A  (b = 0),   A = max_{(t,y) bad, mu(t)>0 reachable} E_{M(t,y)} phi  when N >= 1
(in the free-task model; with a task stream the attacker can only use tasks that arrive)."""
import random
from fractions import Fraction as Fr
rng = random.Random(3)

def sample(d):
    u, acc = rng.random(), 0.0
    for k, p in d.items():
        acc += p
        if u < acc: return k
    return k

def simulate(T, mu, Y, Bad, M, PH, phi, pi, r, b, N, nh, kill, trials=60000):
    cats = 0
    for _ in range(trials):
        # honeypot phase
        alive, misses = True, 0
        for _ in range(nh):
            ty = sample(PH); z = sample(M[ty])
            if rng.random() < phi[z]:
                if rng.random() < kill(misses): alive = False; break
                misses += 1
        if not alive: continue
        u, hist = 0, ()
        for _ in range(N):
            t = sample(mu); y = sample(pi(hist, t)); z = sample(M[(t, y)])
            if rng.random() < phi[z]:
                if (t, y) in Bad: cats += 1; break
                hist += ((t, y, z, True),)
            else:
                if u < b:
                    if (t, y) in Bad:
                        if rng.random() >= r: cats += 1
                        break
                    u += 1; hist += ((t, y, z, False),)
                else:
                    break  # halt (safe)
    return cats / trials

def surv(q, phi, kill, n, j):
    if n == 0: return 1.0
    return sum(q[z] * ((1 - phi[z]) * surv(q, phi, kill, n-1, j) + phi[z] * (1 - kill(j)) * surv(q, phi, kill, n-1, j+1)) for z in q)

def cat(T, mu, Y, Bad, M, phi, pi, r, b, n, u, h):
    if n == 0: return 0.0
    tot = 0.0
    for t in T:
        for y, py in pi(h, t).items():
            for z, mz in M[(t, y)].items():
                pv = 1.0 if (t, y) in Bad else cat(T, mu, Y, Bad, M, phi, pi, r, b, n-1, u, h + ((t, y, z, True),))
                fv = ((1 - r) if (t, y) in Bad else cat(T, mu, Y, Bad, M, phi, pi, r, b, n-1, u+1, h + ((t, y, z, False),))) if u < b else 0.0
                tot += mu[t] * py * mz * (phi[z] * pv + (1 - phi[z]) * fv)
    return tot

T = ["t0", "t1"]; Y = ["ok", "bd"]; Z = ["z0", "z1", "z2"]
worst = 0
for trial in range(12):
    mu = {"t0": 0.6, "t1": 0.4}
    Bad = {("t1", "bd"), ("t0", "bd")}
    M = {}
    for t in T:
        for y in Y:
            w = [rng.random() for _ in Z]; s = sum(w); M[(t, y)] = {z: v / s for z, v in zip(Z, w)}
    PH = {("t0", "bd"): 0.5, ("t1", "bd"): 0.5}
    q = {z: sum(PH[k] * M[k][z] for k in PH) for z in Z}
    phi = {z: rng.random() for z in Z}
    # an adaptive generator: attack on t1 only after one passed benign submission
    def pi(hist, t):
        if t == "t1" and any(v for (_, _, _, v) in hist): return {"bd": 1.0}
        return {"ok": 0.7, "bd": 0.3} if t == "t1" else {"ok": 1.0}
    r, b, N, nh = 0.8, 1, 3, 3
    kill = lambda j: 1 if j >= 1 else 0
    rec = surv(q, phi, kill, nh, 0) * cat(T, mu, Y, Bad, M, phi, pi, r, b, N, 0, ())
    sim = simulate(T, mu, Y, Bad, M, PH, phi, pi, r, b, N, nh, kill)
    worst = max(worst, abs(rec - sim))
print(f"recurrence vs independent Monte Carlo (60k runs x 12 instances): max |diff| = {worst:.4f} (MC s.e. ~0.002)")

# exact deployment value (free-task model: mu concentrated per attack) via DP over deterministic adaptive generators
def best(Bad, M, phi, r, b, N, X):
    from functools import lru_cache
    @lru_cache(None)
    def V(n, u):
        if n == 0: return 0.0
        vals = []
        for x in X:
            s = 0.0
            for z, mz in M[x].items():
                pv = 1.0 if x in Bad else V(n-1, u)
                fv = ((1 - r) if x in Bad else V(n-1, u+1)) if u < b else 0.0
                s += mz * (phi[z] * pv + (1 - phi[z]) * fv)
            vals.append(s)
        return max(vals)
    return V(N, 0)
mx = 0
for trial in range(300):
    X = ["b1", "b2", "a1", "a2"]; Bad = {"a1", "a2"}
    M = {}
    for x in X:
        w = [rng.random() for _ in Z]; s = sum(w); M[x] = {z: v / s for z, v in zip(Z, w)}
    phi = {z: rng.choice([0.0, 1.0, rng.random()]) for z in Z}
    r = rng.random(); b = rng.choice([0, 1, 2]); N = rng.choice([1, 2, 3])
    A = max(sum(M[x][z] * phi[z] for z in Z) for x in Bad)
    claim = (1 - r + r * A) if b > 0 else A
    mx = max(mx, abs(best(Bad, M, phi, r, b, N, X) - claim))
print(f"exact deployment value 1-r+rA (b>0) / A (b=0): max |DP - formula| over 300 instances = {mx:.2e}")
