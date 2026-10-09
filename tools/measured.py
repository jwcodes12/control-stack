#!/usr/bin/env python3
"""Measured premises -> exact one-sided Clopper-Pearson bounds (and Lean terms for ControlStack/Core/Measured.lean).

    python3 tools/measured.py [--delta 0.05] [--json] [--measurement-only] [--lean [OUT.lean]]

Reads recorded evidence only (verdicts / receipts / results under scenarios/*/evidence and the LLM evaluations'
evidence directories); makes no model calls and changes nothing. For every MEASUREMENT-kind premise of
ASSURANCE-LEDGER.md (and a few rates recorded for other premises, shown with their kind) it reports, per data
source:

  successes k of n trials of the GOOD event (caught / accepted / removed / correct; failure rates are flipped so
  every bound is a LOWER bound on a good rate), the point estimate, and

      r_low(k, n, delta) = the largest r with P_r(S >= k) <= delta          (S ~ Bin(n, r))

  i.e. the exact one-sided Clopper-Pearson lower bound: for every true p, P_p(p < r_low(S)) <= delta
  (`Measured.cp_valid`; the preregistered threshold form is `Measured.cp_threshold`). r_low is found by bisection on
  the regularized incomplete beta (scenarios/SC-21/harness/stats.py), rounded DOWN to a 6-digit rational r0, and
  P_{r0}(S >= k) <= delta is then re-checked EXACTLY in integer arithmetic (the `check` column).

The CAVEAT column is part of the result. A bound on a POPULATION rate (over the tasks / attacks / trials the
evidence drew) is not a per-history guarantee (`Measured.population_not_per_history`); toy tasks, scripted
repetitions and a single host limit what the number means. See docs/MEASUREMENT.md.

--lean emits, for each row, a theorem instantiating `ControlStack.Measured.cp_threshold` with these numbers; the tail
inequality is a hypothesis `htail` discharged here by the exact check, not by Lean. Skipped (with a message) when
ControlStack/Core/Measured.lean or the expected names are absent.
"""
import argparse
import glob
import hashlib
import json
import math
import os
import re
import sys
from fractions import Fraction

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(REPO, "ASSURANCE-LEDGER.md")
MEASURED_LEAN = os.path.join(REPO, "ControlStack", "Core", "Measured.lean")
DIGITS = 6                     # r0 = floor(r_low * 10^DIGITS) / 10^DIGITS

sys.dont_write_bytecode = True
try:                           # reuse the SC-21 incomplete beta when importable
    sys.path.insert(0, os.path.join(REPO, "scenarios", "SC-21", "harness"))
    from stats import binom_sf as _sc21_binom_sf  # noqa: E402
except Exception:              # pragma: no cover - fallback below
    _sc21_binom_sf = None
finally:
    sys.path.pop(0)


# ---------------------------------------------------------------- binomial tail and the bound

def binom_sf_float(k, n, p):
    """P(S >= k), S ~ Bin(n, p), float"""
    if k <= 0:
        return 1.0
    if k > n:
        return 0.0
    if p <= 0:
        return 0.0
    if p >= 1:
        return 1.0
    if _sc21_binom_sf is not None:
        return _sc21_binom_sf(k, n, p)
    # log-space direct sum (fallback)
    lo = [math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) + i * math.log(p) + (n - i) * math.log1p(-p)
          for i in range(k, n + 1)]
    m = max(lo)
    return math.exp(m) * sum(math.exp(x - m) for x in lo)


def tail_exact(k, n, r):
    """P_r(S >= k) exactly, as (numerator, denominator) integers, r a Fraction in [0, 1]; integer recursion over the
    shorter side (no gcd reduction: the numbers can have millions of bits)"""
    r = Fraction(r)
    if k <= 0:
        return 1, 1
    if k > n:
        return 0, 1
    a, D = r.numerator, r.denominator
    b = D - a
    den = D ** n
    if b == 0:
        return 1, 1
    if k - 1 <= n - k:         # 1 - P(S <= k-1): k terms; T_i = C(n,i) a^i b^(n-i)
        T, tot = b ** n, 0
        for i in range(k):
            tot += T
            T = T * (n - i) * a // ((i + 1) * b)
        return den - tot, den
    T, tot = math.comb(n, k) * a ** k * b ** (n - k), 0
    for i in range(k, n + 1):
        tot += T
        if i < n:
            T = T * (n - i) * a // ((i + 1) * b)
    return tot, den


def ratio_float(num, den):
    if num == 0:
        return 0.0
    return math.exp(math.log(num) - math.log(den))


def cp_lower(k, n, delta):
    """float r_low: largest r with P_r(S >= k) <= delta (0 if k == 0)"""
    if n == 0 or k == 0:
        return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if binom_sf_float(k, n, mid) <= delta:
            lo = mid
        else:
            hi = mid
    return lo


def certified_lower(k, n, delta):
    """(r0 Fraction, tail float): r0 = r_low rounded down to DIGITS, with P_{r0}(S >= k) <= delta checked exactly"""
    delta = Fraction(delta).limit_denominator(10 ** 9)
    if n == 0 or k == 0:
        return Fraction(0), 1.0
    scale = 10 ** DIGITS
    r0 = Fraction(math.floor(cp_lower(k, n, float(delta)) * scale), scale)
    while r0 > 0:
        num, den = tail_exact(k, n, r0)
        if num * delta.denominator <= delta.numerator * den:
            return r0, ratio_float(num, den)
        r0 -= Fraction(1, scale)
    return Fraction(0), 1.0


# ---------------------------------------------------------------- ledger

def read_ledger(path=LEDGER):
    """premise -> {kind, scenarios}"""
    out = {}
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    for line in lines:
        m = re.match(r"\|\s*\d+\s*\|\s*\*\*([a-z_]+)\*\*:[^|]*\|\s*([a-z_]+)\s*\|\s*\d+\s*\|\s*([^|]*)\|", line)
        if m:
            out[m.group(1)] = {"kind": m.group(2), "scenarios": re.findall(r"SC-\d+", m.group(3))}
    return out


# ---------------------------------------------------------------- data sources

def rel(p):
    return os.path.relpath(p, REPO)


def sha256(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def load(p):
    with open(p, encoding="utf-8") as f:
        return json.load(f)


SCRIPTED = "unit = one scripted repetition of a deterministic workload (nominal rate); single host"
TOY_LLM = "toy task; one model, CLI-default sampling; population over the preregistered task set; single host"
POP = "population rate, not per-history (Measured.population_not_per_history)"

# (premise, scenario, prereg hypothesis, label) for runtime harness usefulness hypotheses (prereg section 4)
USEFULNESS_H = [("SC-07", "H3"), ("SC-08", "H4"), ("SC-12", "H3"), ("SC-14", "H5"), ("SC-15", "H4"), ("SC-16", "H4"),
                ("SC-17", "H4"), ("SC-18", "H4"), ("SC-19", "H5"), ("SC-20", "H4"), ("SC-23", "H3"), ("SC-25", "H4"),
                ("SC-27", "H2")]


def row(premise, scenario, label, k, n, path, caveat, unit):
    return {"premise": premise, "scenario": scenario, "label": label, "k": int(k), "n": int(n), "unit": unit,
            "source": rel(path), "sha256": sha256(path), "caveat": caveat}


def src_harness_usefulness():
    for sc, h in USEFULNESS_H:
        for p in sorted(glob.glob(os.path.join(REPO, "scenarios", sc, "evidence", "run-*", "verdicts.json"))):
            v = load(p).get("per_hypothesis", {}).get(h)
            if v:
                yield row("honest_usefulness", sc, "%s usefulness reps passed (%s)" % (h, os.path.basename(
                    os.path.dirname(p))), v["passed"], v["reps"], p, SCRIPTED, "repetition")


def src_sc26():
    for p in sorted(glob.glob(os.path.join(REPO, "scenarios", "SC-26", "evidence", "run-*", "receipt.json"))):
        u = load(p).get("phases", {}).get("usefulness")
        if u and "success" in u:
            yield row("honest_usefulness", "SC-26", "H4 honest invoices paid (%s, %d crash-injected)" % (
                os.path.basename(os.path.dirname(p)), u.get("crash_injected", 0)), u["success"], u["n"], p,
                "scripted honest invoices with injected crashes; single host", "invoice")
    p = os.path.join(REPO, "scenarios", "SC-26", "llm_eval", "evidence", "run-1", "receipt.json")
    if os.path.exists(p):
        s = load(p)["summary"]["honest"]
        yield row("honest_usefulness", "SC-26", "LLM agent honest gated tasks succeed (U1)", s["successes"],
                  s["tasks"], p, TOY_LLM, "task")
    p = os.path.join(REPO, "scenarios", "SC-26", "llm_approver", "evidence", "run-1", "receipt.json")
    if os.path.exists(p):
        s = load(p)["summary"]
        for arm in ("H-free", "H-struct"):
            if arm in s:
                yield row("honest_usefulness", "SC-26", "LLM approver accepts honest PO requests (%s)" % arm,
                          s[arm]["po_requests"] - s[arm]["false_rejects"], s[arm]["po_requests"], p, TOY_LLM, "request")
        for arm in ("A-free", "A-free-sonnet"):
            if arm in s:
                yield row("semantic_judgement", "SC-26", "LLM approver rejects non-PO requests (%s red team)" % arm,
                          s[arm]["non_po_requests"] - s[arm]["unauthorized_approvals"], s[arm]["non_po_requests"], p,
                          TOY_LLM + "; adaptive red-team requests are not i.i.d.; " + POP, "request")


def src_sc22():
    p = os.path.join(REPO, "scenarios", "SC-22", "evidence", "run-1", "results.jsonl")
    if not os.path.exists(p):
        return
    det = {"k": 0, "n": 0}
    hon = {"k": 0, "n": 0}
    with open(p, encoding="utf-8") as f:
        lines = f.readlines()
    for line in lines:
        r = json.loads(line)
        st = r.get("raw", {}).get("structural")
        if r["hyp"] == "H1" and st:
            for v in st.values():
                det["n"] += v["trials"]
                det["k"] += v["trials"] - v["n_defects"]
        if r["hyp"] == "H2" and st:
            hon["n"] += st["trials"]
            hon["k"] += st["trials"] - st["n_defects"]
    cav = "simulated two-process protocol; trials share one code path (not independent failure modes); single host"
    if det["n"]:
        yield row("semantic_judgement", "SC-22", "replication verdict = (sample meets misreports), H1 trials",
                  det["k"], det["n"], p, cav + "; " + POP, "trial")
    if hon["n"]:
        yield row("semantic_judgement", "SC-22", "honest reports not flagged (H2 trials)", hon["k"], hon["n"], p, cav,
                  "trial")


def src_sc21():
    p = os.path.join(REPO, "scenarios", "SC-21", "harness", "evidence", "run-1", "raw.json")
    if not os.path.exists(p):
        return
    raw = load(p)
    base = [r for r in raw if r.get("mutation") is None]
    n = sum(r["trials"] for r in base)
    k = n - sum(r["detection_violations"] for r in base)
    yield row("deterministic_reexecution", "SC-21", "audited re-execution detects (no detection violation)", k, n, p,
              "simulated pipeline; tasks deterministic by construction; trials share one code path", "trial")
    for r in base:
        if r["adversary"] == "fixed" and r["r"] == "1" and r["q"] == 0.0:
            yield row("hidden_sample", "SC-21", "k=%d misreports detected by the hidden sample (N=%d, B=%d)" % (
                r["k"], r["N"], r["B"]), r["trials"] - r["hidden_success"], r["trials"], p,
                "simulated sampler; exact value is 1 - C(N-k,B)/C(N,B); validates the sampler, not a deployment",
                "trial")


def src_sc24():
    p = os.path.join(REPO, "scenarios", "SC-24", "llm_collusion", "evidence", "run-1", "receipt.json")
    if os.path.exists(p) and load(p).get("summary"):
        s = load(p)["summary"]
        hp = s["pass_rates"]
        for key, label in (("honest/raw/honeypot", "honest monitor flags honeypots (raw)"),
                           ("honest/raw/attack_word", "honest monitor flags word attacks (raw)")):
            x = hp[key]
            yield row("semantic_judgement", "SC-24", label, x["n"] - x["pass"], x["n"], p, TOY_LLM + "; " + POP,
                      "item")
        x = s["signal"]["word/attack_word/canon"]
        yield row("honeypot_indistinguishable", "SC-24", "V1 word signal removed by the canonicaliser",
                  x["n"] - x["pass"], x["n"], p, TOY_LLM + "; one fixed signal; detector-restricted", "item")
        c4 = s["C4"]["correct_canon"]
        yield row("honest_usefulness", "SC-24", "V1 canonical honest answers correct", c4["pass"], c4["n"], p,
                  TOY_LLM, "item")
    p = os.path.join(REPO, "scenarios", "SC-24", "llm_collusion_v2", "evidence", "run-1", "receipt.json")
    if os.path.exists(p) and load(p).get("summary"):
        c0 = load(p)["summary"]["C0_pooled_content_free_survival"]
        yield row("honeypot_indistinguishable", "SC-24", "V2 content-free signals removed by the canonicaliser",
                  c0["n"] - c0["k"], c0["n"], p,
                  TOY_LLM + "; 7 fixed families, NOT adaptive; items clustered by problem; detector-restricted",
                  "item")


SOURCES = [src_harness_usefulness, src_sc26, src_sc22, src_sc21, src_sc24]
PENDING = [("SC-24", "scenarios/SC-24/llm_collusion/evidence/run-1"),
           ("SC-24", "scenarios/SC-24/llm_collusion_v2/evidence/run-1")]


def collect(delta, ledger, measurement_only=False):
    rows, notes = [], []
    for src in SOURCES:
        for r in src():
            info = ledger.get(r["premise"], {})
            r["kind"] = info.get("kind", "unknown")
            r["ledger_member"] = r["scenario"] in info.get("scenarios", [])
            if measurement_only and r["kind"] != "measurement":
                continue
            r0, tail = certified_lower(r["k"], r["n"], delta)
            r.update({"point": round(r["k"] / r["n"], 6) if r["n"] else None, "delta": delta,
                      "r_low": float(r0), "r_low_rational": "%d/%d" % (r0.numerator, r0.denominator),
                      "tail_at_r_low": tail, "check": "exact (integer arithmetic)"})
            rows.append(r)
    for sc, d in PENDING:
        if os.path.isdir(os.path.join(REPO, d)) and not os.path.exists(os.path.join(REPO, d, "receipt.json")):
            notes.append("%s: %s has no receipt.json yet (run in progress?); skipped" % (sc, d))
    have = {r["premise"] for r in rows}
    for prem, info in sorted(ledger.items()):
        if info["kind"] == "measurement" and prem not in have:
            notes.append("measurement premise %s: no recorded binomial data" % prem)
    return rows, notes


# ---------------------------------------------------------------- output

def table(rows, notes, delta):
    hdr = ["premise", "kind", "scenario", "member", "measured (good event)", "k/n", "point", "r_low@δ=%g" % delta,
           "source", "sha256", "caveat"]
    lines = ["| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)]
    for r in rows:
        lines.append("| " + " | ".join([
            r["premise"], r["kind"], r["scenario"], "yes" if r["ledger_member"] else "no", r["label"],
            "%d/%d" % (r["k"], r["n"]), "%.4f" % r["point"], "%.4f" % r["r_low"], r["source"], r["sha256"][:12],
            r["caveat"]]) + " |")
    if notes:
        lines += [""] + ["- " + n for n in notes]
    return "\n".join(lines)


LEAN_NAMES = [r"noncomputable def tailP\b", r"\bdef cnt\b", r"\bdef wB\b", r"theorem cp_threshold\b",
              r"namespace ControlStack\.Measured\b"]


def lean_snippet(rows, delta):
    if not os.path.exists(MEASURED_LEAN):
        return None, "ControlStack/Core/Measured.lean not found; --lean skipped"
    with open(MEASURED_LEAN, encoding="utf-8") as f:
        src = f.read()
    missing = [n for n in LEAN_NAMES if not re.search(n, src)]
    if missing:
        return None, "Measured.lean lacks %s; --lean skipped" % missing
    d = Fraction(delta).limit_denominator(10 ** 9)
    out = ["/- Generated by tools/measured.py from recorded evidence (delta = %s). Each theorem instantiates" % d,
           "   ControlStack.Measured.cp_threshold: if S >= k then report r0, valid at level delta. The tail inequality",
           "   `htail` is checked EXACTLY by tools/measured.py (integer arithmetic) and is a hypothesis here, not a",
           "   Lean proof. A certificate using r0 adds delta to its bound (Measured.ProbCert.ofMeasured: b + delta)",
           "   and inherits the CAVEAT: a population rate is not a per-history rate. -/",
           "import ControlStack.Core.Measured", "", "namespace ControlStack.MeasuredInstances", "",
           "open ControlStack.Measured", ""]
    for i, r in enumerate(rows):
        if r["k"] == 0:
            continue
        name = "m%02d_%s_%s" % (i, r["premise"], r["scenario"].replace("-", ""))
        out += ["/-- %s / %s: %s; %d/%d, r0 = %s (exact tail %.3g); source %s (sha256 %s). CAVEAT: %s -/" % (
                    r["premise"], r["scenario"], r["label"], r["k"], r["n"], r["r_low_rational"], r["tail_at_r_low"],
                    r["source"], r["sha256"][:16], r["caveat"]),
                "theorem %s (htail : tailP %d %d (%s : ℝ) ≤ (%s : ℝ)) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :" % (
                    name, r["n"], r["k"], r["r_low_rational"], d),
                "    ∑ x : Fin %d → Bool, (if p < (if %d ≤ cnt x then (%s : ℝ) else 0) then wB p x else 0)" % (
                    r["n"], r["k"], r["r_low_rational"]),
                "      ≤ (%s : ℝ) :=" % d,
                "  cp_threshold %d %d (%s : ℝ) (%s : ℝ) (by norm_num) (by norm_num) (by norm_num) htail p hp" % (
                    r["n"], r["k"], r["r_low_rational"], d), ""]
    out += ["end ControlStack.MeasuredInstances", ""]
    return "\n".join(out), None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--delta", type=float, default=0.05)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--measurement-only", action="store_true", help="only premises of kind measurement")
    ap.add_argument("--lean", nargs="?", const="-", default=None, help="emit the Lean snippet (to a file or stdout)")
    a = ap.parse_args(argv)
    if not 0 < a.delta < 1:
        ap.error("--delta must be in (0, 1)")
    rows, notes = collect(a.delta, read_ledger(), a.measurement_only)
    if a.lean is not None:
        snip, why = lean_snippet(rows, a.delta)
        if snip is None:
            print(why, file=sys.stderr)
        elif a.lean == "-":
            print(snip)
            return 0
        else:
            with open(a.lean, "w", encoding="utf-8") as f:
                f.write(snip)
            print("wrote %s (%d theorems)" % (a.lean, snip.count("\ntheorem ")), file=sys.stderr)
    if a.json:
        print(json.dumps({"delta": a.delta, "rows": rows, "notes": notes}, indent=1))
    else:
        print(table(rows, notes, a.delta))
    return 0


if __name__ == "__main__":
    sys.exit(main())
