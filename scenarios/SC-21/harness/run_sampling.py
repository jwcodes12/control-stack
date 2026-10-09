#!/usr/bin/env python3
"""SC-21 empirical validation of the proved sampling bounds (no LLM; standard library only).

    python3 scenarios/SC-21/harness/run_sampling.py --out DIR [--trials 2000] [--seed dry] [--label dry|evidence]

Compares empirical survival in the pipeline (`pipeline.py`) with the exact values proved in Lean:
  C(N−k,B)/C(N,B)  (EvalIntegrity.sc21_undetected_prob, EvalIntegrityAdaptive.sc21_adaptive)
  hypMiss N B k r  (EvalIntegrityAdaptive.sc21_adaptive_recall, ReservedRecall.hypMiss)
Parameters N = 100, B = 10, k ∈ {1, 3, 5}, r ∈ {1, 1/2}; leak correlation q ∈ {0, 1/4, 1/2, 1}.
Hypotheses and tests (preregistered in prereg/SC21-SAMPLING.md):
  H1 fixed / pace / burst at r = 1: one-sided exact binomial test of H0 "p <= bound"; no rejection at the Bonferroni
     level 0.01/18 (shared with H3).
  H2 fixed at r ∈ {1, 1/2}: the two-sided Clopper–Pearson interval at level 1 − 0.01/6 contains the exact value.
  H3 fixed / pace / burst at r = 1/2 (recall event): as H1 against hypMiss.
  H4 leak, r = 1: for q ∈ {1/4, 1/2, 1} the one-sided test REJECTS "p <= bound" at level 0.01/9, and for each k the
     point estimates increase strictly in q over {0, 1/4, 1/2, 1}.
  H5 structural checks pass on every main configuration (zero detection violations at r = 1, sample-inclusion
     uniformity, deterministic re-execution) and every mutation is caught by its check.
"""
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from fractions import Fraction
from statistics import NormalDist
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE))
import pipeline as PL  # noqa: E402
import stats as ST  # noqa: E402

N, B = 100, 10
KS = (1, 3, 5)
RS = (Fraction(1), Fraction(1, 2))
QS = (0.0, 0.25, 0.5, 1.0)
ALPHA = 0.01
EVIDENCE_TRIALS = 20000
EVIDENCE_SEED = "sc21-sampling-evidence-v1"
PREREG = REPO / "prereg" / "SC21-SAMPLING.md"
EVIDENCE_DIR = HERE / "evidence"
N_CONFIGS = 3 * len(RS) * len(KS) + len(QS) * len(KS) + 1  # main configurations + the self-check baseline
# uniformity: Bonferroni over every task of every checked configuration, two-sided, family level ALPHA
Z_CRIT = NormalDist().inv_cdf(1 - ALPHA / (2 * N * N_CONFIGS))


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-C", str(REPO)] + list(args), capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def exact(k, r):
    return ST.bound_hidden(N, B, k) if r == 1 else ST.hyp_miss(N, B, k, r)


def row(res, k, r, event):
    x, n = res[event + "_success"], res["trials"]
    ex = exact(k, r)
    return {"cfg": res["cfg"], "adversary": res["adversary"], "k": k, "r": str(r), "q": res["q"], "event": event,
            "successes": x, "trials": n, "empirical": x / n, "exact": str(ex), "exact_float": float(ex),
            "p_one_sided_le": ST.binom_sf(x, n, float(ex)), "reached_k": res["reached_k"],
            "detection_violations": res["detection_violations"]}


def evaluate(main, trials):
    out = {}
    h1 = [r for r in main if r["adversary"] in ("fixed", "pace", "burst") and r["r"] == "1"]
    h3 = [r for r in main if r["adversary"] in ("fixed", "pace", "burst") and r["r"] == "1/2"]
    a13 = ALPHA / (len(h1) + len(h3))
    for name, rows in (("H1", h1), ("H3", h3)):
        bad = [r["cfg"] for r in rows if r["p_one_sided_le"] < a13]
        out[name] = {"pass": not bad, "alpha_per_test": a13, "tests": len(rows), "rejected": bad}
    h2 = [r for r in main if r["adversary"] == "fixed"]
    lvl = 1 - ALPHA / len(h2)
    fails = []
    for r in h2:
        lo, hi = ST.clopper_pearson(r["successes"], r["trials"], lvl)
        r["ci"] = [lo, hi]
        if not lo <= r["exact_float"] <= hi:
            fails.append(r["cfg"])
    out["H2"] = {"pass": not fails, "level": lvl, "tests": len(h2), "excluded_exact": fails}
    leak = [r for r in main if r["adversary"] == "leak"]
    pos = [r for r in leak if r["q"] > 0]
    a4 = ALPHA / len(pos)
    not_exceeding = [r["cfg"] for r in pos if not r["p_one_sided_le"] < a4]
    mono = {}
    for k in KS:
        est = [next(r["empirical"] for r in leak if r["k"] == k and r["q"] == q) for q in QS]
        mono[k] = {"q": list(QS), "empirical": est, "strictly_increasing": all(a < b for a, b in zip(est, est[1:]))}
    out["H4"] = {"pass": not not_exceeding and all(m["strictly_increasing"] for m in mono.values()),
                 "alpha_per_test": a4, "not_exceeding_bound": not_exceeding, "monotone": mono}
    return out


def self_check(trials, seed):
    """H5: the baseline passes its structural checks and every mutation is caught"""
    t = min(trials, 2000)
    base = PL.run_config(N, B, 3, 1, "fixed", t, seed + "/self")
    nore = PL.run_config(N, B, 3, 1, "fixed", t, seed + "/self", mutation="no_reexec")
    bias = PL.run_config(N, B, 3, 1, "fixed", t, seed + "/self", mutation="biased_sample")
    checks = {
        "baseline_detection": base["detection_violations"] == 0,
        "baseline_uniform": PL.uniformity_check(base["inclusion"], t, N, B, Z_CRIT)[0],
        "baseline_deterministic": PL.determinism_check(N),
        "mutant_no_reexec_caught": nore["detection_violations"] > 0,
        "mutant_biased_sample_caught": not PL.uniformity_check(bias["inclusion"], t, N, B, Z_CRIT)[0],
        "mutant_nondet_task_caught": not PL.determinism_check(N, mutation="nondet_task", repeats=50),
    }
    return {"pass": all(checks.values()), "trials": t, "checks": checks,
            "no_reexec_violations": nore["detection_violations"],
            "biased_sample_zmax": PL.uniformity_check(bias["inclusion"], t, N, B, Z_CRIT)[1]}


def evidence_refusal(a):
    if not PREREG.exists():
        return "prereg missing"
    text = PREREG.read_text()
    if "Status: DRAFT" in text:
        return "prereg is still a DRAFT"
    if os.environ.get("SC21_SAMPLING_PREREG_SHA256") != sha(PREREG):
        return "env SC21_SAMPLING_PREREG_SHA256 must equal sha256 of prereg/SC21-SAMPLING.md"
    if EVIDENCE_DIR.resolve() not in a.out.resolve().parents:
        return "--out must be under " + str(EVIDENCE_DIR)
    if a.seed != EVIDENCE_SEED or a.trials != EVIDENCE_TRIALS:
        return "evidence runs use seed %s and %d trials" % (EVIDENCE_SEED, EVIDENCE_TRIALS)
    st = git("status", "--porcelain", "--", str(HERE.relative_to(REPO)), str(PREREG.relative_to(REPO)))
    if st:
        return "harness and prereg must be committed and unmodified: " + st[:300]
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--trials", type=int, default=2000)
    ap.add_argument("--seed", default="dry")
    ap.add_argument("--label", default="dry", choices=["dry", "evidence"])
    a = ap.parse_args()
    if a.label == "evidence":
        why = evidence_refusal(a)
        if why:
            raise SystemExit("refusing evidence label: " + why)
    elif EVIDENCE_DIR.resolve() in a.out.resolve().parents or a.seed == EVIDENCE_SEED:
        raise SystemExit("dry runs must not write under the evidence directory or use the evidence seed")
    if a.out.exists():
        raise SystemExit("refusing to overwrite " + str(a.out))
    a.out.mkdir(parents=True)
    t0 = time.monotonic()
    raw, main_rows, structural = [], [], []
    for adv in ("fixed", "pace", "burst"):
        for r in RS:
            for k in KS:
                res = PL.run_config(N, B, k, r, adv, a.trials, a.seed)
                raw.append(res)
                main_rows.append(row(res, k, r, "hidden" if r == 1 else "recall"))
    for q in QS:
        for k in KS:
            res = PL.run_config(N, B, k, Fraction(1), "leak", a.trials, a.seed, q=q)
            raw.append(res)
            main_rows.append(row(res, k, Fraction(1), "hidden"))
    for res in raw:
        ok, z = PL.uniformity_check(res["inclusion"], res["trials"], N, B, Z_CRIT)
        structural.append({"cfg": res["cfg"], "uniform": ok, "zmax": round(z, 3),
                           "detection_violations": res["detection_violations"]})
    hyp = evaluate(main_rows, a.trials)
    sc = self_check(a.trials, a.seed)
    struct_ok = all(s["uniform"] and s["detection_violations"] == 0 for s in structural) and PL.determinism_check(N)
    hyp["H5"] = {"pass": sc["pass"] and struct_ok, "self_check": sc, "structural_all_configs": struct_ok}
    receipt = {"label": a.label, "seed": a.seed, "trials_per_config": a.trials, "N": N, "B": B, "ks": KS,
               "rs": [str(r) for r in RS], "qs": QS, "alpha": ALPHA, "z_crit_uniformity": Z_CRIT, "python": sys.version, "platform":
               platform.platform(), "git_commit": git("rev-parse", "HEAD"),
               "code_sha256": {f.name: sha(f) for f in sorted(HERE.glob("*.py"))},
               "prereg_sha256": sha(PREREG) if PREREG.exists() else None, "wall_s": round(time.monotonic() - t0, 1),
               "hypotheses": hyp, "verdict": "PASS" if all(h["pass"] for h in hyp.values()) else "FAIL"}
    for r in raw:
        r["inclusion"] = None
    (a.out / "rows.json").write_text(json.dumps(main_rows, indent=1))
    (a.out / "structural.json").write_text(json.dumps(structural, indent=1))
    (a.out / "raw.json").write_text(json.dumps(raw, indent=1, default=str))
    (a.out / "receipt.json").write_text(json.dumps(receipt, indent=1, default=str))
    for r in main_rows:
        print("{:<46} emp {:.4f}  exact {:.4f}  p(<=) {:.3g}".format(r["cfg"], r["empirical"], r["exact_float"],
                                                                     r["p_one_sided_le"]))
    print(json.dumps({k: v["pass"] for k, v in hyp.items()}), receipt["verdict"], receipt["wall_s"], "s")
    return 0 if receipt["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
