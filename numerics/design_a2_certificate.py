"""Exact-rational, illustrative Design A2 certificate-table generator.

This is a computational design fixture, not empirical ROC evidence or a Lean theorem.
It models a 100-problem, 2-audit-coin GAC game with a two-vertex ROC uncertainty set.
The emitted JSON records exact inputs suitable for transcribing into checkRiskQ.
"""
from fractions import Fraction as F
import csv
import json
from pathlib import Path

N, COINS = 100, 2
STATES, ACTIONS, MODELS = COINS + 1, 2, 2
# Illustrative rational threshold schedule. At zero coins, the audit path runs code,
# so its false-positive rate is zero. Defer threshold is the same at every state.
def qa(c):
    return F(0) if c == 0 else F(1, 50)

def qd(c):
    return F(49, 100)

# Placeholder enclosure, deliberately not presented as sampled confidence bands.
# A real deployment replaces this two-vertex set with rational simultaneous bands.
SLOPES = (F(2), F(3))
def roc(slope, q):
    return min(F(1), slope * q)

def model_row(slope, c, backdoor):
    audit_tpr = roc(slope, qa(c))
    defer_tpr = roc(slope, qd(c))
    if backdoor:
        cat = 1 - defer_tpr if c > 0 else 1 - defer_tpr + audit_tpr
        # Deferral is the only continuing outcome for a backdoor.
        trans = [F(0)] * STATES
        trans[c] = defer_tpr - audit_tpr
    else:
        cat = F(0)
        trans = [F(0)] * STATES
        if c > 0:
            trans[c - 1] += qa(c)
            trans[c] += 1 - qa(c)
        else:
            trans[c] = 1
    assert cat >= 0 and all(x >= 0 for x in trans) and cat + sum(trans) <= 1
    return cat, trans

# Rows match checkRiskQ's dimensions: theta, horizon index, state, action.
# Action 0 is Safe and action 1 is Backdoor (the Bool order in the Lean game).
cat = [[[[F(0) for _a in range(ACTIONS)] for _s in range(STATES)] for _i in range(N)] for _t in range(MODELS)]
K = [[[[[F(0) for _sp in range(STATES)] for _a in range(ACTIONS)] for _s in range(STATES)] for _i in range(N)] for _t in range(MODELS)]
for t, slope in enumerate(SLOPES):
    for i in range(N):
        for c in range(STATES):
            for a in range(ACTIONS):
                cat[t][i][c][a], K[t][i][c][a] = model_row(slope, c, bool(a))

def row_value(t, i, c, a, v):
    return cat[t][i][c][a] + sum(K[t][i][c][a][sp] * v[sp] for sp in range(STATES))

def best_row(i, c, a, v):
    # Rectangular uncertainty: the model vertex may be selected at each row.
    return max(row_value(t, i, c, a, v) for t in range(MODELS))

# Backward finite-horizon certificate, represented in checkRiskQ's increasing index.
V = [[F(0) for _c in range(STATES)] for _i in range(N + 1)]
for i in range(N):
    for c in range(STATES):
        V[i + 1][c] = max(best_row(i, c, a, V[i]) for a in range(ACTIONS))

# Fixed-rate witnesses: exact risk for the best beta on a 1/100 grid.
def memoryless(beta):
    v = [F(0)] * STATES
    for i in range(N):
        nv = []
        for c in range(STATES):
            attack = best_row(i, c, 1, v)
            safe = best_row(i, c, 0, v)
            nv.append(beta * attack + (1 - beta) * safe)
        v = nv
    return v[COINS]

fixed = max((memoryless(F(j, 100)), F(j, 100)) for j in range(101))

# A clocked witness family: attack exactly in the final j problems; action depends
# only on the public round index. It is a lower bound on the unrestricted clocked class.
def clocked(j):
    v = [F(0)] * STATES
    for i in range(N):
        remaining = N - i
        a = int(remaining <= j)
        v = [best_row(i, c, a, v) for c in range(STATES)]
    return v[COINS]

clock_j = 50
clock_risk = clocked(clock_j)

def honest_used(m, c):
    if m == 0:
        return F(0)
    q_a, q_d = qa(c), qd(c)
    reward = 1 - q_d + (q_a if c > 0 else F(0))
    if c == 0:
        return reward + honest_used(m - 1, 0)
    return reward + q_a * honest_used(m - 1, c - 1) + (1 - q_a) * honest_used(m - 1, c)

used = honest_used(N, COINS)

# Serialize fractions as numerator/denominator strings: no float enters any result.
def q(x):
    return f"{x.numerator}/{x.denominator}"

def nested(x):
    if isinstance(x, list):
        return [nested(y) for y in x]
    return q(x)

out = {
    "description": "Illustrative exact-rational design fixture; not sampled ROC evidence.",
    "dimensions": {"N": N, "states": STATES, "actions": ACTIONS, "models": MODELS},
    "state_labels": ["0 coins", "1 coin", "2 coins"],
    "action_labels": ["safe", "backdoor"],
    "roc_vertices": [f"f(q)=min(1,{q(s)}*q)" for s in SLOPES],
    "thresholds": {"qa(c>0)": q(F(1, 50)), "qa(c=0)": "0/1", "qd": q(F(49, 100))},
    "honest_used_solutions": q(used),
    "checkRiskQ_input": {"cat": nested(cat), "K": nested(K), "V": nested(V)},
    "witnesses": {
        "fixed_rate_grid_1_over_100": {"beta": q(fixed[1]), "risk": q(fixed[0])},
        "clocked_attack_only_final_50": {"j": clock_j, "risk": q(clock_risk)},
        "full_information_rectangular_upper": q(V[N][COINS]),
    },
}
root = Path(__file__).resolve().parent
(root / "design_a2_certificate.json").write_text(json.dumps(out, indent=2) + "\n")
with (root / "design_a2_value_table.csv").open("w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["horizon_steps", "risk_bound_0_coins", "risk_bound_1_coin", "risk_bound_2_coins"])
    for i, row in enumerate(V):
        w.writerow([i, *(q(x) for x in row)])
print(f"generated {N+1} exact certificate rows; {MODELS*N*STATES*ACTIONS} checker inequalities")
print("memoryless grid witness beta/risk:", q(fixed[1]), q(fixed[0]))
print("clocked attack-only-final-50 witness/risk:", clock_j, q(clock_risk))
print("honest expected used solutions:", q(used), "per task", q(used / N))
print("full-information rectangular certificate:", q(V[N][COINS]))
print("wrote numerics/design_a2_certificate.json and numerics/design_a2_value_table.csv")
