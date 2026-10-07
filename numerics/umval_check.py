"""Exact (rational) check of UMVAL (b),(c) against the Lean-draft recursions surv/cat/protocolCat."""
from fractions import Fraction as Fr
from math import comb
import random
rng = random.Random(5)

def surv(q, phi, kill, n, j):
    if n == 0: return Fr(1)
    return sum(q[z] * ((1 - phi[z]) * surv(q, phi, kill, n-1, j) + phi[z] * (1 - kill(j)) * surv(q, phi, kill, n-1, j+1)) for z in q)

def cat(X, Bad, M, phi, pi, r, b, n, u, h):
    if n == 0: return Fr(0)
    tot = Fr(0)
    for x in X:
        px = pi(h)[x]
        if px == 0: continue
        s = Fr(0)
        for z, mz in M[x].items():
            passv = 1 if x in Bad else cat(X, Bad, M, phi, pi, r, b, n-1, u, h + ((x, z, True),))
            if u < b:
                flagv = (1 - r) if x in Bad else cat(X, Bad, M, phi, pi, r, b, n-1, u+1, h + ((x, z, False),))
            else:
                flagv = 0
            s += mz * (phi[z] * passv + (1 - phi[z]) * flagv)
        tot += px * s
    return tot

def push(M, P):
    out = {}
    for x, px in P.items():
        for z, mz in M[x].items():
            out[z] = out.get(z, Fr(0)) + px * mz
    return out

def rq(k):  # random rational distribution of size k
    w = [Fr(rng.randint(0, 5)) for _ in range(k)]
    if sum(w) == 0: w[0] = Fr(1)
    return [v / sum(w) for v in w]

for trial in range(60):
    C = ["A", "B", "C"]
    X = [f"x{i}" for i in range(5)]
    c = {x: C[i % 3] for i, x in enumerate(X)}
    Bad = {"x0", "x1", "x2", "x4"}
    # content-preserving randomised M: views tagged by content
    M = {}
    for x in X:
        w = rq(2); M[x] = {(c[x], v): w[v] for v in range(2) if w[v] > 0}
    wPH = rq(4); PH = {x: wv for x, wv in zip(sorted(Bad), wPH)}
    q = push(M, PH)
    for z in {(e, v) for e in C for v in range(2)}: q.setdefault(z, Fr(0))
    clsmass = {e: sum(PH.get(x, 0) for x in X if c[x] == e) for e in C}
    nh, ns, b, N = rng.randint(0, 4), rng.randint(0, 2), rng.randint(0, 2), rng.randint(1, 2)
    hard = lambda j: 1 if ns <= j else 0
    # (c): exact attainment with xs = x1, t random rational
    xs = "x1"; t = Fr(rng.randint(0, 4), 4); p = clsmass[c[xs]]
    phi = {z: (t if z[0] == c[xs] else Fr(0)) for z in q}
    pi = lambda h: {x: (1 if x == xs else 0) for x in X}
    val = surv(q, phi, hard, nh, 0) * cat(X, Bad, M, phi, pi, Fr(1), b, N, 0, ())
    formula = t * sum(comb(nh, j) * (t * p) ** j * (1 - t * p) ** (nh - j) for j in range(ns + 1))
    assert val == formula, (val, formula)
    # (b): S = {x0, x1, x2} distinct classes A,B,C; colluder on least-covered class
    S = ["x0", "x1", "x2"]; estar_x = min(S, key=lambda x: clsmass[c[x]])
    phi2 = {z: (Fr(1) if z[0] == c[estar_x] else Fr(0)) for z in q}
    pi2 = lambda h: {x: (1 if x == estar_x else 0) for x in X}
    r = Fr(rng.randint(0, 4), 4)
    val2 = surv(q, phi2, hard, nh, 0) * cat(X, Bad, M, phi2, pi2, r, b, N, 0, ())
    assert val2 >= (1 - Fr(1, len(S))) ** nh, (val2,)
print("UMVAL (b) no-go and (c) exact attainment: hold exactly on 60 random rational instances")
