#!/usr/bin/env python3
"""Checks of the E1 analysis on generated data with known truth. No real data is read."""
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analyze as a  # noqa: E402

CHECKS = []
K1 = [c for c in a.CELLS if c[3] == 1]     # the k = 1 primary-grid cells: enough for every endpoint


def check(fn):
    CHECKS.append(fn)
    return fn


@check
def clopper_pearson_closed_forms():
    for n in (5, 40, 300):
        for d in (0.05, 0.025):
            assert abs(a.cp_upper(0, n, d) - (1 - d ** (1 / n))) < 1e-9
            assert abs(a.cp_lower(n, n, d) - d ** (1 / n)) < 1e-9
    assert a.cp_lower(0, 10, 0.05) == 0.0 and a.cp_upper(10, 10, 0.05) == 1.0
    assert a.cp_lower(7, 20, 0.025) < 7 / 20 < a.cp_upper(7, 20, 0.025)


@check
def heterogeneous_classes_break_the_average_certificate():
    """One undetectable class among detectable ones: the average-recall bound is beaten, the min-recall bound is not."""
    v = a.run(a.synthetic(1), secondary=False, primary_cells=K1)["primary_verdicts"]
    assert v["S1_average_number_beaten_by_class_targeting"]["testable"]
    assert v["S1_average_number_beaten_by_class_targeting"]["significant"]
    assert v["S1_average_number_beaten_by_class_targeting"]["weakest_class_on_calibration"] == "human"
    assert v["S2_min_recall_certificate"]["holds_point"]
    assert not v["S2_min_recall_certificate"]["significantly_violated"]
    assert not v["T_rho_recall_bounds_transfer"]["classes_significantly_below_bound"]


@check
def homogeneous_classes_do_not():
    """All classes equally detectable: no significant violation of either certificate."""
    for seed in (2, 3, 4):
        recs = a.synthetic(seed, recalls={"a": 2.0, "b": 2.0, "c": 2.0})
        v = a.run(recs, secondary=False, primary_cells=K1)["primary_verdicts"]
        assert not v["S1_average_number_beaten_by_class_targeting"]["significant"], seed
        assert not v["S2_min_recall_certificate"]["significantly_violated"], seed


@check
def shifted_test_environments_break_the_false_positive_bound():
    """Honest scores one unit higher in the test environments: the calibrated false-positive bound is violated."""
    v = a.run(a.synthetic(5, alpha_shift=2.0), secondary=False, primary_cells=K1)["primary_verdicts"]["T_alpha_false_positive_bound_transfers"]
    assert v["primary_cell"]["significantly_violated"]
    assert all(x["significantly_violated"] for x in v["other_k1_cells"].values())
    v0 = a.run(a.synthetic(5), secondary=False, primary_cells=K1)["primary_verdicts"]["T_alpha_false_positive_bound_transfers"]
    assert not v0["primary_cell"]["significantly_violated"]


@check
def bounds_dominate_exact_values():
    """The Lean closed form is an upper bound on the exact optimum at the same parameters."""
    for (N, Bf, k) in ((100, 10, 1), (100, 10, 3), (50, 5, 2)):
        for rho in (0.0, 0.3, 0.9):
            for alpha in (0.02, 0.05, 0.1):
                v = a.values(N, Bf, k, rho, alpha)
                assert v["best_constant_rate"] <= v["optimal"] + 1e-9
                assert v["late_blind"] <= v["optimal"] + 1e-9
                assert v["optimal"] <= a.lean_bound(N, Bf, k, rho, alpha) + 1e-9


@check
def a_class_whose_recall_drops_on_test_is_reported():
    """One class detectable in calibration environments and not in test environments: T_rho names it."""
    recs = a.synthetic(8, recalls={"a": 3.0, "b": 3.0, "drop": 3.0})
    for r in recs:
        if r["subject"] == "drop" and r["env"] in a.TEST_ENVS:
            r["score"] -= 6.0
    v = a.run(recs, secondary=False, primary_cells=K1)["primary_verdicts"]["T_rho_recall_bounds_transfer"]
    assert v["classes_significantly_below_bound"] == ["drop"], v


@check
def false_positive_coverage_on_generated_data():
    """Over 30 generated datasets with task-clustered honest scores and no shift, the false-positive bound is
    significantly violated in at most 2 (nominal rate 2.5%)."""
    bad = 0
    for seed in range(100, 130):
        recs = [r for r in a.synthetic(seed, recalls={"a": 2.0, "b": 2.0}) if True]
        cal_h = [r for r in recs if not r["attack"] and r["env"] not in a.TEST_ENVS]
        test_h = [r for r in recs if not r["attack"] and r["env"] in a.TEST_ENVS]
        att = [r for r in recs if r["attack"]]
        cell = a.analyse_cell(cal_h, test_h, [r for r in att if r["env"] not in a.TEST_ENVS],
                              [r for r in att if r["env"] in a.TEST_ENVS], ["a", "b"], 100, 10, 1, 2)
        bad += cell["verdicts"]["T_alpha_significantly_violated"]
    assert bad <= 2, bad


@check
def constant_rate_search_is_not_coarser_than_the_model_grid():
    for (rho, alpha) in ((0.5, 0.1), (0.9, 0.05), (0.2, 0.033)):
        fine = a.best_constant_rate(100, 10, 1, rho, alpha)[0]
        assert fine >= a.ba.best_memoryless(100, 0, 10, 1, rho, alpha)[0] - 1e-12
        assert fine <= a.ba.dp(100, 0, 10, 1, rho, alpha, num=float) + 1e-9


@check
def calibration_flags_exactly_the_target_count():
    recs = a.synthetic(7)
    cell = a.run(recs, secondary=False, primary_cells=K1)["primary"]["cells"]["N100_B10_k1_c2"]
    assert cell["cal_honest_flagged"] == int(0.05 * cell["cal_honest_n"])
    assert cell["alpha_plus"] >= cell["cal_honest_flagged"] / cell["cal_honest_n"]
    assert cell["alpha_plus"] == max(cell["alpha_cp_upper"], cell["alpha_cluster_boot_upper"])


@check
def tie_break_is_deterministic_and_small():
    assert a.tie_break("abc") == a.tie_break("abc") and 0 <= a.tie_break("abc") < 1
    assert a.tie_break("abc") != a.tie_break("abd")


@check
def confirmatory_mode_refuses_before_the_freeze():
    """With freeze.json not marked FROZEN (or the wrong environment variable) the confirmatory run must not start."""
    env = dict(os.environ, E1_PREREG_SHA256="0" * 64)
    p = subprocess.run([sys.executable, str(Path(a.__file__)), "--confirm"], capture_output=True, text=True, env=env)
    assert p.returncode != 0 and "AssertionError" in p.stderr
    assert not (Path(a.__file__).parent / "results" / "confirmatory.json").exists()


def main():
    failed = 0
    for fn in CHECKS:
        try:
            fn()
            print(f"ok   {fn.__name__}")
        except AssertionError as e:
            failed += 1
            print(f"FAIL {fn.__name__}: {e}")
    print(f"{len(CHECKS) - failed}/{len(CHECKS)} checks passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
