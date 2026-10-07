"""Assurance manifests for empirical certificates, and a checker that never promotes one evidence category into another.

Categories (each claim must carry exactly one):
  THEOREM_VERIFIED       - a Lean theorem, kernel-checked, standard axioms (statement hash recorded)
  STATISTICALLY_SUPPORTED- a confidence statement from a preregistered analysis of recorded data (data hashes recorded)
  RUNTIME_VALIDATED      - enforced/observed by an instrumented runtime (evidence file recorded)
  UNRESOLVED             - an assumption nobody has discharged
A certificate is reported as DEPLOYMENT-GRADE only if every assumption of the theorem is THEOREM_VERIFIED,
STATISTICALLY_SUPPORTED for the target deployment population, or RUNTIME_VALIDATED. Otherwise the checker prints the
blocking assumptions.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CATS = {"THEOREM_VERIFIED", "STATISTICALLY_SUPPORTED", "RUNTIME_VALIDATED", "UNRESOLVED"}


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


# Assumptions of the DESIGN-A2 / TMCERTF1 certificate pipeline, with their default status.
BASE_ASSUMPTIONS = [
    ("checker_soundness", "THEOREM_VERIFIED", "TMCERTF1 soundness + checkRiskQ/checkLawfulQ by decide +kernel"),
    ("band_coverage", "STATISTICALLY_SUPPORTED", "simultaneous Clopper-Pearson bands cover the true rates (IID sampling)"),
    ("iid_sampling", "UNRESOLVED", "evaluation trajectories are an IID draw from the evaluated population"),
    ("population_match", "UNRESOLVED", "evaluated honest/attack populations equal the deployment's"),
    ("attack_content_coverage", "UNRESOLVED", "Red's reachable attacks are covered by the evaluated attack population "
                                              "(ComposeBlindSpot: averages do not bound a content-adaptive Red)"),
    ("abstraction_coverage", "UNRESOLVED", "TMCERT (Abs): the concrete protocol's rows lie in the interval model"),
    ("timing_pre_execution", "UNRESOLVED", "flags act BEFORE the action takes effect (fails for live failures with "
                                            "trajectory-level scores)"),
    ("monitor_frozen_stateless", "UNRESOLVED", "the monitor is frozen and stateless across calls (A1, A2)"),
    ("absorbing_shutdown_budget", "UNRESOLVED", "audit budget and absorbing shutdown are enforced (A5, A11)"),
]


def manifest(name, prereg, cert_json, lean_file, lean_status, data_files, population, confidence, extra=None):
    c = json.loads((ROOT / cert_json).read_text())
    V = c["checkRiskQ_input"]["V"]
    m = {
        "name": name,
        "theorem": {"id": "PL_TMCERTF1 (full_information_risk_bound via checkRiskQ)",
                    "statement_sha256": sha(ROOT / "ledger" / "TMCERT.lean"),
                    "lean_file": lean_file, "lean_status": lean_status},
        "preregistration": {"file": prereg, "sha256": sha(ROOT / prereg)},
        "protocol": {"game": "DESIGN-A2 trusted monitoring", "thresholds": c["thresholds"],
                     "horizon": c["dimensions"]["N"], "audit_coins": 2, "catastrophe": "uncaught bad submission"},
        "data": {f: sha(ROOT / f) for f in data_files},
        "statistics": {"confidence": confidence, "method": "Clopper-Pearson + Bonferroni", "population": population},
        "result": {"risk_upper": {"N=1": V[1][2], "N=10": V[10][2], "N=100": V[100][2]},
                   "honest_used_lower_per_100": c["honest_used_solutions_lower_simple"]},
        "assumptions": [{"id": a, "status": s, "text": t} for a, s, t in BASE_ASSUMPTIONS],
    }
    if lean_status != "passed":
        for a in m["assumptions"]:
            if a["id"] == "checker_soundness":
                a.update(status="UNRESOLVED", text=a["text"] + f" [Lean check {lean_status}]")
    for k, v in (extra or {}).items():
        for a in m["assumptions"]:
            if a["id"] == k:
                a.update(v)
    return m


def check(m: dict) -> tuple[str, list[str]]:
    for a in m["assumptions"]:
        if a["status"] not in CATS:
            raise ValueError(f"{m['name']}: unknown status {a['status']}")
        if a["status"] == "THEOREM_VERIFIED" and m["theorem"]["lean_status"] != "passed":
            raise ValueError(f"{m['name']}: {a['id']} claims THEOREM_VERIFIED but the Lean check has not passed")
    blocking = [a["id"] for a in m["assumptions"] if a["status"] == "UNRESOLVED"]
    return ("DEPLOYMENT-GRADE" if not blocking else "CONDITIONAL"), blocking


def main() -> int:
    out = ROOT / "assurance"
    ms = []
    ms.append(manifest("lastraj", "PREREG-LASTRAJ.md", "numerics/lastraj_certificate.json",
                       "numerics/lastraj_certificate.lean", "passed",
                       ["data/redwood-leaderboard/monitors.json"], "LaStraj 2.0, 30 honest / 17 attack", "95%"))
    ms.append(manifest("linuxarena-217-split-opus", "PREREG-LINUXARENA-SPLIT.md",
                       "numerics/linuxarena_split/primary_opus.cert.json", "numerics/linuxarena_split/primary.lean",
                       sys.argv[1] if len(sys.argv) > 1 else "pending",
                       ["data/linuxarena/linuxarena-217.json"],
                       "honest: 3 certification environments; attacks: all 10 environments (MISMATCHED)", "95%",
                       {"population_match": {"text": "honest from 3 environments, attacks from 10; matched-population "
                                                     "TPR is lower (numerics/stat_audit.json)"}}))
    for p in sorted((ROOT / "numerics/lasr_test").glob("*.cert.json")):
        tag = p.name.replace(".cert.json", "")
        ms.append(manifest(f"lasr-test/{tag}", "PREREG-LASR-TEST.md", f"numerics/lasr_test/{p.name}",
                           f"numerics/lasr_test/{tag}.lean", "passed", [f"numerics/lasr_test/{tag}.bands.json"],
                           "LASR held-out test split, one condition", "95% family-wise over 42 conditions"))
    summary = []
    for m in ms:
        verdict, blocking = check(m)
        m["verdict"] = verdict
        m["blocking"] = blocking
        (out / (m["name"].replace("/", "__") + ".json")).write_text(json.dumps(m, indent=1) + "\n")
        summary.append((m["name"], verdict, len(blocking)))
    for n, v, b in summary[:3]:
        print(f"{n:<60} {v:<17} {b} unresolved assumptions")
    print(f"... {len(summary)} manifests; deployment-grade: {sum(1 for _, v, _ in summary if v == 'DEPLOYMENT-GRADE')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
