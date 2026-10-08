#!/usr/bin/env python3
"""ctrlcert: conditional control bounds, what refutes them, and what it would take to reach a target.

Every number is printed with (a) the Lean theorem it instantiates, (b) the premises it is conditional on and
(c) the measurement that would refute a premise. No output is a safety certificate. Standard library only;
`diagnose` additionally imports the repo's numerics/ (run from a checkout).

  channel   exact-recovery bound for a finite-view mediated channel with (stateful, adaptive) side channels
  probe     does a measured side-channel recovery rate refute the side-certificate premise?
  audit     adaptive k-step attacker vs a hidden random audit schedule, optionally with leakage about it
  hazard    multi-step survival from a CONDITIONAL per-step catch rate (and why marginal rates do not suffice)
  samples   how many samples a zero-miss estimate needs to certify a miss rate (or refute a side certificate)
  diagnose  for a DESIGN-A2 bands file: is the certified risk dominated by statistical margin, the monitor or the
            protocol? (point-estimate game vs certified game)

`--lean FILE` (channel, audit) writes a Lean file that instantiates the general theorem at the given numbers and
checks the arithmetic; compile it with `lake env lean FILE` from the repo root.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def frac(s: str) -> F:
    s = s.strip()
    if s.startswith("2^"):
        return F(2) ** int(s[2:])
    return F(s)


def fmt(x: F | float) -> str:
    x = float(x)
    if x == 0:
        return "0"
    if abs(x) < 1e-3:
        return f"{x:.4e} (2^{math.log2(x):.2f})"
    return f"{x:.6g}"


def emit(result: dict, args) -> None:
    if getattr(args, "json", False):
        print(json.dumps(result, indent=1, default=str))
        return
    for k, v in result.items():
        if isinstance(v, list):
            print(f"{k}:")
            for item in v:
                print(f"  - {item}")
        else:
            print(f"{k}: {v}")


# ---------- binomial helpers (exact, rational) ----------

def binom_tail_ge(n: int, k: int, p: F) -> F:
    """P(X >= k), X ~ Bin(n, p), exact"""
    return sum((F(math.comb(n, j)) * p ** j * (1 - p) ** (n - j) for j in range(k, n + 1)), F(0))


def cp_lower(n: int, x: int, alpha: F, grid: int = 100000) -> F:
    """one-sided Clopper–Pearson lower bound on a grid of 1/grid, rounded outward (down)"""
    if x == 0:
        return F(0)
    lo, hi = 0, grid
    # largest p on the grid with P(X >= x | p) <= alpha
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if binom_tail_ge(n, x, F(mid, grid)) <= alpha:
            lo = mid
        else:
            hi = mid - 1
    return F(lo, grid)


# ---------- channel ----------

def cmd_channel(args):
    bits, V, n = args.secret_bits, args.views, args.episodes
    lam = [frac(x) for x in args.side_mass.split(",")] if args.side_mass else [F(1)]
    if len(lam) == 1:
        lam = lam * n
    if len(lam) != n:
        sys.exit("--side-mass needs one value or one per episode")
    M = F(2) ** bits
    views = F(V) ** n
    side = math.prod(lam, start=F(1))
    bound = min(F(1), views * side / M)
    res = {
        "bound": f"P(exact recovery) <= {fmt(bound)}  = |V|^n * prod(lambda) / 2^bits = {V}^{n} * {fmt(side)} / 2^{bits}",
        "theorem": "Leakage.covert_side_bound (general); Leakage.sc01_adaptive_target (|V|=9, n=5, 32 bits); "
                   "CovertChannel.covert_bound_lifetime when lambda = 1",
        "tight_when": "lambda = 1: attained by an injective code (CovertChannel.attain_embedding) when |V|^n <= 2^bits",
        "premises": [
            "the secret is uniform and independent of the shared seed and of the receiver's inputs "
            "(witness: Necessity.seed_secret_breaks_covert)",
            f"the receiver observes exactly {n} views from a set of {V} (fixed count; a visible, encoder-controlled "
            "count adds the views of every shorter transcript: ScenarioACore.varObs_breaks_target)",
            "everything else the receiver observes comes through side kernels whose per-episode certificate mass, "
            "given the visible history, is <= lambda_i (kernels may carry state between episodes; the sender may see "
            "side outputs). The certificate must dominate the JOINT side output of an episode "
            "(witness: Necessity.marginal_certs_dont_compose)",
            "the harm is exact recovery of the secret; low-bandwidth coordination is NOT bounded "
            "(CovertNoGo.one_bit_coordinates: one distinguishable bit coordinates with certainty)",
        ],
        "refuted_by": "a side-channel probe with recovery rate p (one bit, constant view) whose one-sided lower bound "
                      "has 2*p_lo > allowed side mass; see `ctrlcert probe`",
    }
    if args.target:
        T = frac(args.target)
        allowed = T * M / views
        res["target"] = f"{fmt(T)}: {'MET' if bound <= T else 'NOT MET'} by this bound"
        res["allowed_total_side_mass"] = (f"prod(lambda) <= {fmt(allowed)} "
                                          f"(per episode, uniform: {fmt(float(allowed) ** (1 / n))})")
        res["one_clean_side_bit"] = (f"mass 2 -> bound {fmt(min(F(1), 2 * views / M))}: "
                                     f"{'breaks' if 2 * views / M > T else 'keeps'} the target")
        if bound > T:
            # smallest secret length / fewest episodes meeting the target
            need_bits = math.ceil(math.log2(float(views * side / T)))
            res["to_meet_target"] = [f"secret of >= {need_bits} bits, or",
                                     f"<= {max(0, math.floor(math.log(float(T * M / side), V)))} episodes of {V} views"]
    emit(res, args)
    if args.lean:
        write_channel_lean(args.lean, V, n, bits, lam, args.target and frac(args.target))
        print(f"lean: wrote {args.lean}; check with `lake env lean {args.lean}`", file=sys.stderr)


def lean_q(x: F) -> str:
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"


def write_channel_lean(path, V, n, bits, lam, target):
    lam_def = " | ".join([f"{i} => {lean_q(l)}" for i, l in enumerate(lam)] + ["_ => 1"])
    prod_val = math.prod(lam, start=F(1))
    target_part = ""
    if target is not None:
        bound = F(V) ** n * prod_val / F(2) ** bits
        rel, name = ("≤", "ctrlcert_channel_target") if bound <= target else (">", "ctrlcert_channel_target_missed")
        target_part = f"""
/-- the arithmetic: |V|^n · Π λ / 2^bits {rel} target ({'met' if rel == '≤' else 'NOT met by this bound'}) -/
theorem {name} : ({V} : ℝ) ^ {n} * {lean_q(prod_val)} / (2 : ℝ) ^ {bits} {rel} {lean_q(target)} := by
  norm_num
"""
    Path(path).write_text(f"""/- emitted by tools/ctrlcert.py channel: |V| = {V}, n = {n}, secret bits = {bits}, per-episode side
masses λ = {[str(l) for l in lam]}. Instantiates Leakage.covert_side_bound; all premises are hypotheses. -/
import ControlStack.Leakage

open ControlStack.Leakage ControlStack.Covert Finset

noncomputable def ctrlcertLam : ℕ → ℝ := fun i => match i with | {lam_def}

theorem ctrlcert_lam_prod : ∏ i ∈ range {n}, ctrlcertLam i = {lean_q(prod_val)} := by
  norm_num [Finset.prod_range_succ, ctrlcertLam]

theorem ctrlcert_channel {{Ω Y Z : Type}} [Fintype Ω] [Fintype Y] [Fintype Z]
    (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ {bits}) → List (Y × (Fin {V} × Z)) → Y × (Fin {V} × Z) → ℝ)
    (cs : List (Fin {V} × Z) → Z → ℝ) (dec : Ω → List (Fin {V} × Z) → Fin (2 ^ {bits}) → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2))
    (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ ctrlcertLam g.length)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ {bits})) : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) {n} [])
      ≤ ({V} : ℝ) ^ {n} * {lean_q(prod_val)} / (2 : ℝ) ^ {bits} := by
  have h := covert_side_bound ρ K cs ctrlcertLam dec {n} hρ hK0 hdom hcs0 hlam
    (fun i => by unfold ctrlcertLam; split <;> norm_num) hdec
  rw [ctrlcert_lam_prod] at h
  refine h.trans (le_of_eq ?_)
  norm_num
{target_part}""")


# ---------- probe ----------

def cmd_probe(args):
    M = F(2) ** args.secret_bits
    views = F(args.views) ** args.episodes
    allowed = frac(args.target) * M / views
    alpha = frac(args.alpha)
    p_lo = cp_lower(args.n, args.correct, alpha)
    mass_lower = F(2) ** args.probe_bits * p_lo
    refuted = mass_lower > allowed
    res = {
        "measured": f"{args.correct}/{args.n} recoveries of a uniform {args.probe_bits}-bit probe secret with a "
                    f"constant mediated view",
        "one_sided_lower": f"{p_lo} ({fmt(p_lo)}) at confidence 1 - {alpha} (Clopper–Pearson, rounded down)",
        "certificate_mass_lower": f"every side certificate has mass >= 2^{args.probe_bits} * p_lo = {fmt(mass_lower)}",
        "allowed_mass": f"{fmt(allowed)} for target {args.target} with {args.views}^{args.episodes} views and "
                        f"{args.secret_bits}-bit secret",
        "verdict": "REFUTED: the side-certificate premise is false for this harness" if refuted else
                   "NOT REFUTED at this power (this does not establish the premise)",
        "theorem": "SafetyCaseSC01.bit_refutes (probe_bits = 1); the general form is the transfer bound read "
                   "backwards (Leakage.transfer: success <= mass * blind value)",
        "premises": ["trials are independent with a common recovery probability (binomial)",
                     "the probe's side kernel is the deployment's side kernel (same host, same configuration)"],
    }
    if not refuted and args.correct == args.n:
        need = math.ceil(math.log(float(alpha)) / math.log(float(allowed / F(2) ** args.probe_bits))) \
            if allowed < F(2) ** args.probe_bits else None
        res["trials_to_refute_if_all_correct"] = need if need else "impossible: allowed mass >= 2^probe_bits"
    emit(res, args)
    return 3 if refuted else 0


# ---------- audit ----------

def hyper(N, B, k) -> F:
    return F(math.comb(N - k, B), math.comb(N, B))


def one_bit_leak_exact(N, B, k) -> F:
    """exact optimal survival when Red learns, before round 1, whether one fixed round r is audited"""
    p_aud = F(B, N)
    s_aud = F(math.comb(N - 1 - k, B - 1), math.comb(N - 1, B - 1)) if B >= 1 else F(1)
    s_free = F(math.comb(N - 1 - (k - 1), B), math.comb(N - 1, B))
    return p_aud * s_aud + (1 - p_aud) * s_free


def cmd_audit(args):
    N, B, k = args.rounds, args.budget, args.steps
    if not (0 <= B <= N and 1 <= k <= N):
        sys.exit("need 0 <= B <= N and 1 <= k <= N")
    h = hyper(N, B, k)
    L = frac(args.leak_mass) if args.leak_mass else F(1)
    res = {
        "hidden_schedule": f"survival <= C(N-k,B)/C(N,B) = {fmt(h)} for EVERY adaptive attacker that sees its own "
                           f"actions and catch flags (Leakage.audit_adaptive_hidden); <= ((N-B)/N)^k = "
                           f"{fmt(F(N - B, N) ** k)} (AuditBudget.survival_le_pow)",
        "with_leak": f"leak certificate mass L = {fmt(L)}: survival <= min(1, L * {fmt(h)}) = {fmt(min(F(1), L * h))} "
                     "(Leakage.audit_leak_bound / audit_leak_prod; catch flags cost nothing, cval_live)",
        "observable_schedule": f"survival = 1 when N - B >= k ({N - B} >= {k}: {N - B >= k}) "
                               "(AuditBudget.observable_schedule_nogo); the leak bound is vacuous there "
                               f"(L = C(N,B) = {math.comb(N, B)})",
        "honest_gap_example": f"one noiseless leaked bit 'is round r audited?': exact optimum "
                              f"{fmt(one_bit_leak_exact(N, B, k))} vs bound 2 * {fmt(h)} = {fmt(min(F(1), 2 * h))} "
                              "(the bound is sound, not tight, for this leak)" if B >= 1 and k <= N - 1 else "n/a",
        "premises": [
            "the schedule is a uniformly random size-B subset of the N rounds, drawn independently of Red",
            "an audit of an attack step catches it with certainty; catching ends the attack",
            "Red needs k attack steps in distinct rounds",
            "honest rounds do not consume audits: the schedule is drawn independently of monitor flags "
            "(with first-come flag-triggered audits this fails; see --fpr)",
            "everything Red learns about the schedule beyond catch flags is dominated by the leak certificate, "
            "given its visible history",
        ],
        "refuted_by": "timing or resource differences between audited and unaudited rounds that Red can measure "
                      "(estimate the leak certificate from a distinguishing experiment)",
    }
    if args.fpr:
        f = frac(args.fpr)
        exhaust = binom_tail_ge(N - k, B, f) if B >= 1 else F(1)
        res["first_come_with_false_positives"] = (
            f"if audits are instead triggered by monitor flags, first come first served, and honest rounds flag at "
            f"rate {fmt(f)}: an attacker that waits for the last {k} rounds finds the budget already spent with "
            f"probability >= P(Bin({N - k}, {fmt(f)}) >= {B}) = {fmt(exhaust)}, and then survives whatever the "
            f"monitor's recall (Necessity.exhausted_no_audit; instance: fp_exhaustion_breaks_audit, 7/8 vs 3/4). "
            f"Expected false positives {fmt(f * (N - k))} vs budget {B}")
    if args.target:
        T = frac(args.target)
        need_B = next((b for b in range(0, N + 1) if L * hyper(N, b, k) <= T), None)
        res["target"] = f"{fmt(T)}: {'MET' if L * h <= T else 'NOT MET'}"
        res["budget_needed"] = (f"B >= {need_B} audits (of N = {N}) for L * C(N-k,B)/C(N,B) <= target"
                                if need_B is not None else "no budget meets the target at this leak mass")
        res["leak_tolerated"] = (f"L <= {fmt(T / h)} at B = {B}" if h and T / h >= 1 else
                                 f"none: even with no leak (L = 1) the target is not met at B = {B}")
    emit(res, args)
    if args.lean:
        write_audit_lean(args.lean, N, B, k)
        print(f"lean: wrote {args.lean}; check with `lake env lean {args.lean}`", file=sys.stderr)


def write_audit_lean(path, N, B, k):
    a, b = math.comb(N - k, B), math.comb(N, B)
    Path(path).write_text(f"""/- emitted by tools/ctrlcert.py audit: N = {N}, B = {B}, k = {k}, no leak.
Instantiates Leakage.audit_adaptive_hidden: every randomised adaptive attacker that sees its own actions and catch
flags survives a hidden uniformly random size-{B} schedule with probability ≤ C({N - k},{B})/C({N},{B}). -/
import ControlStack.Leakage

open ControlStack.Leakage

theorem ctrlcert_choose_num : Nat.choose {N - k} {B} = {a} := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

theorem ctrlcert_choose_den : Nat.choose {N} {B} = {b} := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

theorem ctrlcert_audit (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, ControlStack.Covert.IsDist (σ g)) :
    ∑ S : Finset (Fin {N}), (if S ∈ ControlStack.AuditBudget.randomSchedules {N} {B}
        then (Nat.choose {N} {B} : ℝ)⁻¹ else 0) * val (hiddenK σ S) (survInd {k} S) {N} []
      ≤ ({a} : ℝ) / {b} := by
  have h := audit_adaptive_hidden (N := {N}) {k} {B} (by norm_num) σ hσ
  rw [show {N} - {k} = {N - k} by norm_num, ctrlcert_choose_num, ctrlcert_choose_den] at h
  exact_mod_cast h
""")


# ---------- hazard ----------

def cmd_hazard(args):
    c, k = frac(args.catch), args.steps
    res = {
        "conditional_rate": f"if EVERY step is caught with probability >= {fmt(c)} given the full history, "
                            f"k-step survival <= (1-c)^k = {fmt((1 - c) ** k)} (MultiStep.survival_le)",
        "marginal_rate_only": f"if {fmt(c)} is only a marginal (average) catch rate, misses can be perfectly "
                              f"correlated and survival can be 1-c = {fmt(1 - c)} for every k "
                              "(MultiStep.correlated_nogo)",
        "what_to_measure": "per-step catch rate CONDITIONAL on the attack's earlier steps going uncaught "
                           "(e.g. evaluate step j only on trajectories whose steps < j were missed); an ROC from "
                           "independent single steps is a marginal",
    }
    emit(res, args)


# ---------- samples ----------

def cmd_samples(args):
    alpha = frac(args.alpha)
    res = {}
    if args.target_miss:
        t = frac(args.target_miss)
        n = math.ceil(math.log(float(alpha)) / math.log(1 - float(t)))
        res["zero_miss_samples"] = (f"n >= {n} independent attack samples, all caught, certify a miss rate "
                                    f"<= {fmt(t)} at confidence 1 - {alpha} (exact: (1-t)^n <= alpha)")
        if args.horizon:
            res["horizon_note"] = (f"over {args.horizon} independent attempts a per-attempt miss bound t gives "
                                   f"overall <= 1-(1-t)^N = {fmt(1 - (1 - t) ** args.horizon)}; to reach an overall "
                                   f"target you need t ~ target/N, i.e. N times more samples. If deferred attacks "
                                   f"are not incriminated, this compounding is the protocol, not the statistics: "
                                   f"no sample size fixes it")
    res["premise"] = "samples are independent draws from the deployment attack distribution (coverage)"
    emit(res, args)


# ---------- diagnose ----------

def cmd_diagnose(args):
    sys.path.insert(0, str(ROOT / "numerics"))
    from certificate_decomposition import decompose  # noqa: E402
    d = decompose(Path(args.bands), args.audit, args.defer)
    pt, ce = d["point"], d["certified"]
    if pt[1] >= 0.5 * ce[1] and pt[1] >= 0.2:
        regime = "MONITOR: even with exact rates one round is risky; better monitoring or a different protocol"
    elif pt[100] >= 0.5 * ce[100] and pt[100] >= 0.2:
        regime = ("PROTOCOL: the point-estimate risk compounds over rounds; more data will not help; change the "
                  "protocol (incriminate on defer, resample, scale the budget with N)")
    else:
        regime = ("MARGIN: the certified risk is mostly statistical conservatism; more attack samples, fewer "
                  "simultaneous comparisons or a preregistered single condition will help")
    res = {"point_estimate_risk": {n: round(v, 4) for n, v in pt.items()},
           "certified_risk": {n: round(v, 4) for n, v in ce.items()},
           "regime": regime,
           "caveat": "post hoc descriptive analysis, not a certificate; trajectory-max scores are not online catches"}
    emit(res, args)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("channel"); c.add_argument("--secret-bits", type=int, default=32)
    c.add_argument("--views", type=int, required=True); c.add_argument("--episodes", type=int, required=True)
    c.add_argument("--side-mass", help="lambda (one value or comma list per episode), e.g. 1 or 1.02,1,1,1,1")
    c.add_argument("--target", help="e.g. 2^-16"); c.add_argument("--lean")
    p = sub.add_parser("probe"); p.add_argument("--correct", type=int, required=True)
    p.add_argument("--n", type=int, required=True); p.add_argument("--probe-bits", type=int, default=1)
    p.add_argument("--alpha", default="1/20"); p.add_argument("--secret-bits", type=int, default=32)
    p.add_argument("--views", type=int, default=9); p.add_argument("--episodes", type=int, default=5)
    p.add_argument("--target", default="2^-16")
    a = sub.add_parser("audit"); a.add_argument("--rounds", type=int, required=True)
    a.add_argument("--budget", type=int, required=True); a.add_argument("--steps", type=int, required=True)
    a.add_argument("--leak-mass"); a.add_argument("--target"); a.add_argument("--lean")
    a.add_argument("--fpr", help="honest false-positive rate, for first-come score-triggered auditing")
    h = sub.add_parser("hazard"); h.add_argument("--catch", required=True); h.add_argument("--steps", type=int, required=True)
    s = sub.add_parser("samples"); s.add_argument("--target-miss"); s.add_argument("--alpha", default="1/20")
    s.add_argument("--horizon", type=int)
    d = sub.add_parser("diagnose"); d.add_argument("bands"); d.add_argument("--audit", required=True)
    d.add_argument("--defer", required=True)
    for sp in (c, p, a, h, s, d):
        sp.add_argument("--json", action="store_true")
    args = ap.parse_args()
    rc = {"channel": cmd_channel, "probe": cmd_probe, "audit": cmd_audit, "hazard": cmd_hazard,
          "samples": cmd_samples, "diagnose": cmd_diagnose}[args.cmd](args)
    return rc or 0


if __name__ == "__main__":
    sys.exit(main())
