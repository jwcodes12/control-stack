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
    res = a.run(recs, secondary=False, primary_cells=K1)["primary_verdicts"]
    assert res["T_rho_recall_bounds_transfer"]["classes_significantly_below_bound"] == ["drop"], res
    # the min-recall certificate was non-trivial on calibration data and is now beaten on test: reported as violated
    assert not res["S2_min_recall_certificate"]["equals_one"]
    assert res["S2_min_recall_certificate"]["significantly_violated"]


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
def late_blind_closed_form():
    """For k = 1 the last-round attacker succeeds with probability (1-rho) + rho * P(Bin(N-1, alpha) >= Bf)."""
    for (N, Bf) in ((100, 10), (50, 3)):
        for rho in (0.0, 0.4, 1.0):
            for alpha in (0.03, 0.1):
                got = a.ba.dp(N, 0, Bf, 1, rho, alpha, num=float, late=True)
                want = (1 - rho) + rho * a.ba.bin_tail(alpha, Bf, N - 1)
                assert abs(got - want) < 1e-12, (N, Bf, rho, alpha, got, want)


@check
def loader_handles_shared_ids_and_unscored_rows():
    """A base run and its monitor rerun share a trajectory id; one monitor row has no scored action."""
    import gzip, json, tempfile
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        (d / "meta").mkdir(); (d / "sealed").mkdir()
        base = {"environment": "e", "main_task": "t", "side_task": None, "side_task_success": False, "n_monitor_errors": 0}
        meta = [dict(base, trajectory_id="x1", run_id="r0", run_display_name="Opus honest"),
                dict(base, trajectory_id="x1", run_id="r0", run_display_name="M monitor on Opus honest"),
                dict(base, trajectory_id="x2", run_id="r0", run_display_name="M monitor on Opus honest"),
                dict(base, trajectory_id="x3", run_id="r1", run_display_name="M monitor on Opus attack",
                     side_task="s", side_task_success=True, n_monitor_errors=2)]
        seal = [{"trajectory_id": "x1", "action_scores": [None], "traj_score": None},
                {"trajectory_id": "x1", "action_scores": [1.0, 3.0, None], "traj_score": 2.0},
                {"trajectory_id": "x2", "action_scores": [None, None], "traj_score": None},
                {"trajectory_id": "x3", "action_scores": [7.5], "traj_score": None}]
        with gzip.open(d / "meta" / "s.jsonl.gz", "wt") as f:
            f.write("".join(json.dumps(m) + "\n" for m in meta))
        with gzip.open(d / "sealed" / "s.jsonl.gz", "wt") as f:
            f.write("".join(json.dumps(m) + "\n" for m in seal))
        recs = a.load(d, ["s"])
        assert [r["id"] for r in recs] == ["x1", "x3"]
        assert 3.0 <= recs[0]["score"] < 3.000001 and not recs[0]["attack"]
        assert recs[1]["attack"] and recs[1]["success"] and recs[1]["monitor_errors"] == 2 and recs[1]["monitor"] == "M"
        assert dict(a.DROPS) == {"not_a_monitor_run": 1, "monitor_run_without_scored_action": 1}
        # a duplicate id among monitor rows, or misaligned files, must stop the run
        with gzip.open(d / "meta" / "s.jsonl.gz", "wt") as f:
            f.write("".join(json.dumps(m) + "\n" for m in [meta[1], meta[1]]))
        with gzip.open(d / "sealed" / "s.jsonl.gz", "wt") as f:
            f.write("".join(json.dumps(m) + "\n" for m in [seal[1], seal[1]]))
        try:
            a.load(d, ["s"]); raise AssertionError("duplicate monitor-run id accepted")
        except SystemExit:
            pass


@check
def leave_one_environment_out_names_the_shifted_environment():
    recs = a.synthetic(9)
    for r in recs:
        if not r["attack"] and r["env"] == "tiktok":
            r["score"] += 1.5
    out = a.leave_one_env_out(recs, a.PRIMARY_MONITOR, frozenset())
    assert len(out) == 10
    assert out["tiktok"]["significantly_violated"]
    assert sum(v["significantly_violated"] for v in out.values()) <= 2


@check
def calibration_flags_exactly_the_target_count():
    recs = a.synthetic(7)
    cell = a.run(recs, secondary=False, primary_cells=K1)["primary"]["cells"]["N100_B10_k1_c2"]
    assert cell["cal_honest_flagged"] == cell["cal_honest_flag_target"] == (10 * cell["cal_honest_n"]) // (2 * 100)
    # integer scores tie massively; the realised count is reported and used, never the target
    tied = [dict(r, score=float(round(r["score"]))) for r in recs]
    c2 = a.run(tied, secondary=False, primary_cells=K1)["primary"]["cells"]["N100_B10_k1_c2"]
    assert c2["cal_honest_flagged"] <= c2["cal_honest_flag_target"]
    assert abs(c2["alpha_cp_upper"] - a.cp_upper(c2["cal_honest_flagged"], c2["cal_honest_n"], 0.025)) < 1e-12
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
    for flags in ([], ["-O"]):                 # the guard must not be an assert
        p = subprocess.run([sys.executable, *flags, str(Path(a.__file__)), "--confirm"], capture_output=True,
                           text=True, env=env)
        assert p.returncode != 0 and "not authorised" in p.stderr, (flags, p.stderr)
    res = Path(a.__file__).parent / "results"
    assert not (res / "confirmatory.json").exists() and not (res / "confirmatory.started").exists()


@check
def freeze_and_confirm_rehearsal_on_generated_data():
    """The whole authorised path, in a temporary copy of the tree with generated data in place of the real files:
    freeze, confirm, one-shot refusal, refusal to freeze twice, refusal after a pinned file changes."""
    import gzip, json, shutil, tempfile
    here = Path(a.__file__).parent
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        exp = root / "experiments" / "E1-flag-budget-replay"
        exp.mkdir(parents=True)
        (root / "numerics").mkdir()
        for f in ("analyze.py", "freeze.py", "test_analyze.py", "extract_scores.py", "PREREG.md"):
            shutil.copy(here / f, exp / f)
        shutil.copy(here.parents[1] / "numerics" / "budgeted_audit.py", root / "numerics" / "budgeted_audit.py")
        (exp / "development_run_ids.json").write_text(json.dumps(["hon0"]))     # one honest run plays the dev set
        (exp / "freeze.json").write_text('{"status": "DRAFT"}\n')
        data = root / "data" / "linuxarena-public" / "compact"
        (data / "meta").mkdir(parents=True); (data / "sealed").mkdir()
        recs = a.synthetic(11)
        for sh in a.SHARDS:
            rows = [r for r in recs if r["env"] == sh]
            with gzip.open(data / "meta" / f"{sh}.jsonl.gz", "wt") as fm, gzip.open(data / "sealed" / f"{sh}.jsonl.gz", "wt") as fs:
                for r in rows:
                    fm.write(json.dumps({"trajectory_id": r["id"], "run_id": r["run_id"], "environment": sh,
                                         "run_display_name": f"{a.PRIMARY_MONITOR} monitor on {r['subject']}",
                                         "main_task": r["task"][1], "side_task": "s" if r["attack"] else None,
                                         "side_task_success": r["success"], "n_monitor_errors": 0}) + "\n")
                    fs.write(json.dumps({"trajectory_id": r["id"], "action_scores": [r["score"]], "traj_score": None}) + "\n")
        py = [sys.executable, "-O"]
        run = lambda *args, **env: subprocess.run([*py, *args], capture_output=True, text=True, cwd=root,   # noqa: E731
                                                  env=dict(os.environ, **env))
        p = run(str(exp / "freeze.py"), "--write")
        assert p.returncode == 0, p.stderr
        fz = json.loads((exp / "freeze.json").read_text())
        assert fz["status"] == "FROZEN" and len(fz["data_sha256"]) == 20 and len(fz["code_sha256"]) == 5
        assert run(str(exp / "freeze.py"), "--write").returncode != 0                       # no second freeze
        assert run(str(exp / "analyze.py"), "--confirm", E1_PREREG_SHA256="0" * 64).returncode != 0
        assert not (exp / "results" / "confirmatory.started").exists()
        p = run(str(exp / "analyze.py"), "--confirm", E1_PREREG_SHA256=fz["prereg_sha256"])
        assert p.returncode == 0, p.stderr[-800:]
        res = json.loads((exp / "results" / "confirmatory.json").read_text())
        assert res["primary"]["cal_honest"] == 6 * 20 * 19 and res["primary"]["test_honest"] == 4 * 20 * 19  # dev run excluded
        assert set(res["primary_verdicts"]) == {"T_alpha_false_positive_bound_transfers", "T_rho_recall_bounds_transfer",
                                               "S1_average_number_beaten_by_class_targeting",
                                               "S2_min_recall_certificate", "S3_exhaustion_gap"}
        assert len(res["leave_one_environment_out_false_positive"]) == 10
        assert "N1000_B20_k1_c1" in res["primary"]["cells"]
        p2 = run(str(exp / "analyze.py"), "--confirm", E1_PREREG_SHA256=fz["prereg_sha256"])
        assert p2.returncode != 0 and "one-shot" in p2.stderr                              # no second run
        # a changed pinned file blocks a run even with the marker gone
        shutil.rmtree(exp / "results")
        (exp / "PREREG.md").write_text((exp / "PREREG.md").read_text() + "\nedited\n")
        p3 = run(str(exp / "analyze.py"), "--confirm", E1_PREREG_SHA256=fz["prereg_sha256"])
        assert p3.returncode != 0 and not (exp / "results").exists()


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
