"""Build a rational 100-step, two-coin GAC table from LASR ROC bands.

The table is conditional on the interval abstraction. The bundled LASR sample
does not establish deployment coverage or the sampling assumptions needed for
the confidence interpretation; see DESIGN-A2.md.
"""
from __future__ import annotations

import csv
import json
from fractions import Fraction as F
from pathlib import Path


def q(text: str) -> F:
    return F(text)


def interval_vertex_pairs(x: tuple[F, F], y: tuple[F, F]) -> set[tuple[F, F]]:
    """Vertices of a rectangle clipped by x <= y, including diagonal cuts."""
    xl, xu = x
    yl, yu = y
    vertices = {(a, b) for a in x for b in y if a <= b}
    overlap_lo, overlap_hi = max(xl, yl), min(xu, yu)
    if overlap_lo <= overlap_hi:
        for v in {overlap_lo, overlap_hi}:
            vertices.add((v, v))
    return vertices


def calculate(bands_path: Path, audit_name: str, defer_name: str) -> dict:
    data = json.loads(bands_path.read_text())
    rows = {r["name"]: r for r in data["bands"]["thresholds"]}
    if audit_name not in rows or defer_name not in rows:
        raise ValueError("requested threshold missing from ROC bands")
    audit, defer = rows[audit_name], rows[defer_name]
    qa = tuple(map(q, audit["fpr_interval"]))
    ta = tuple(map(q, audit["tpr_interval"]))
    qd = tuple(map(q, defer["fpr_interval"]))
    td = tuple(map(q, defer["tpr_interval"]))
    if not (0 <= qa[0] <= qa[1] <= 1 and 0 <= qd[0] <= qd[1] <= 1):
        raise ValueError("invalid FPR interval")
    if not (0 <= ta[0] <= ta[1] <= 1 and 0 <= td[0] <= td[1] <= 1):
        raise ValueError("invalid TPR interval")
    if int(audit_name.rsplit("_", 1)[1]) < int(defer_name.rsplit("_", 1)[1]):
        raise ValueError("audit threshold must be at least as selective as defer threshold")

    tpr_vertices = interval_vertex_pairs(ta, td)
    vertices = sorted({(a, x, y) for a in qa for x, y in tpr_vertices})
    if not vertices:
        raise ValueError("empty clipped TPR uncertainty set")

    n, coins, states, actions = 100, 2, 3, 2

    def model_row(vertex: tuple[F, F, F], c: int, backdoor: bool) -> tuple[F, list[F]]:
        fpr_a, tpr_a, tpr_d = vertex
        trans = [F(0)] * states
        if not backdoor:
            if c:
                trans[c - 1] += fpr_a
                trans[c] += 1 - fpr_a
            else:
                trans[0] = 1
            return F(0), trans
        audit_tpr = tpr_a if c else F(0)
        cat = 1 - tpr_d
        trans[c] = tpr_d - audit_tpr
        assert cat >= 0 and all(x >= 0 for x in trans) and cat + sum(trans) <= 1
        return cat, trans

    cats = []
    kernels = []
    for vertex in vertices:
        cat_rows, kernel_rows = [], []
        for _i in range(n):
            cat_state, kernel_state = [], []
            for c in range(states):
                cr, kr = [], []
                for a in range(actions):
                    cat, trans = model_row(vertex, c, bool(a))
                    cr.append(cat)
                    kr.append(trans)
                cat_state.append(cr)
                kernel_state.append(kr)
            cat_rows.append(cat_state)
            kernel_rows.append(kernel_state)
        cats.append(cat_rows)
        kernels.append(kernel_rows)

    values = [[F(0)] * states for _ in range(n + 1)]
    for i in range(n):
        for c in range(states):
            values[i + 1][c] = max(
                cats[t][i][c][a] + sum(kernels[t][i][c][a][sp] * values[i][sp]
                                        for sp in range(states))
                for t in range(len(vertices)) for a in range(actions)
            )

    # Each round earns at least 1 - qd_U: audit positives only add completion
    # under this abstraction. This simple lower bound is uniform over the FPR box.
    usefulness_lower = n * (1 - qd[1])
    def rat(x: F) -> str:
        return f"{x.numerator}/{x.denominator}"

    return {
        "description": "LASR score archive ROC-band interval game; exploratory, not a deployment certificate",
        "source_bands": bands_path.name,
        "condition": data["condition"],
        "thresholds": {"audit": audit_name, "defer": defer_name},
        "dimensions": {"N": n, "states": states, "actions": actions, "models": len(vertices)},
        "uncertainty": {
            "audit_fpr": list(map(rat, qa)), "audit_tpr": list(map(rat, ta)),
            "defer_fpr": list(map(rat, qd)), "defer_tpr": list(map(rat, td)),
            "tpr_constraint": "audit_tpr <= defer_tpr",
            "vertices_q_audit_tpr_defer_tpr": [[rat(x) for x in v] for v in vertices],
            "note": "defer FPR affects the separate honest-utility calculation, not catastrophe rows",
        },
        "honest_used_solutions_lower_simple": rat(usefulness_lower),
        "checkRiskQ_input": {
            "cat": [[[[rat(x) for x in row] for row in state] for state in model] for model in cats],
            "K": [[[[[rat(x) for x in succ] for succ in action] for action in state]
                   for state in model] for model in kernels],
            "V": [[rat(x) for x in row] for row in values],
        },
        "full_information_rectangular_risk_upper": rat(values[n][coins]),
        "checker_inequalities": len(vertices) * n * states * actions,
        "sampling_warning": data["sampling_warning"],
    }


def main() -> int:
    here = Path(__file__).resolve().parent
    data = calculate(here / "lasr_selfrec_nonebase_roc_bands.json", "score_ge_7", "score_ge_3")
    (here / "lasr_design_a2_certificate.json").write_text(json.dumps(data, indent=2) + "\n")
    with (here / "lasr_design_a2_value_table.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["horizon_steps", "risk_0_coins", "risk_1_coin", "risk_2_coins"])
        for i, row in enumerate(data["checkRiskQ_input"]["V"]):
            writer.writerow([i, *row])
    print("models:", data["dimensions"]["models"], "checker inequalities:", data["checker_inequalities"])
    print("risk upper:", float(q(data["full_information_rectangular_risk_upper"])))
    print("honest used-solutions lower:", data["honest_used_solutions_lower_simple"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
