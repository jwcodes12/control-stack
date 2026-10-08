#!/usr/bin/env python3
"""One-command check of the SC-01 conditional safety/usefulness case (ControlStack/SafetyCaseSC01.lean).

Checks, in order, and fails closed on any error:
1. every Lean file of the case compiles (`lake env lean`, writing its .olean so later files can import it), contains no
   sorry/admit/axiom/native_decide, and every listed theorem depends only on propext, Classical.choice, Quot.sound;
2. file hashes match assurance/sc01-safety-case.json (`--update-hashes` rewrites them after an intended change);
3. the Python gateway agrees with the Lean gateway core (gateway/difftest_core.py);
4. the usefulness receipt verifies (gateway/scenario/check_receipt.py) and its lower endpoints equal the
   Lean-certified 93382/100000 at 64/64;
5. the side-certificate hypothesis is evaluated against the cache receipt via `bit_refutes`: a one-sided lower bound
   p_lo on single-bit recovery refutes every certificate of mass <= 65536/59049 when 2 * p_lo > 65536/59049.
Then prints every assumption on separate axes (provenance, testability, refuting experiment, status).

Output keeps four things apart: PROOFS (the Lean statements compile with standard axioms; model-only, not ledger
red-teamed), BINDINGS (hashes), EVIDENCE (receipts verify) and APPLICABILITY (whether measured evidence refutes a
hypothesis of the case). It never prints a bare bound and is never a safety certificate.

Exit codes: 0 = all checks pass and no hypothesis is refuted (verdict CONDITIONAL);
            3 = all checks pass but measured evidence refutes a hypothesis (verdict HYPOTHESIS_REFUTED);
            1 = a check failed (proof, binding, difftest or receipt).
`--json PATH` also writes the result in machine-readable form.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "assurance" / "sc01-safety-case.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_ENV = dict(os.environ, PATH=str(Path.home() / ".elan" / "bin") + os.pathsep + os.environ.get("PATH", ""))


def sha(p):
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()


def fail(msg):
    print("FAIL:", msg)
    print("\nVERDICT: CHECK_FAILED (no conclusion about the case)")
    sys.exit(1)


def check_lean(m, key="lean"):
    count = 0
    build = ROOT / ".lake" / "build" / "lib" / "lean"
    for entry in m.get(key, []):
        f, ns, names = entry["file"], entry["namespace"], entry["theorems"]
        src = (ROOT / f).read_text()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", src, re.M):
            fail(f"{f}: forbidden keyword")
        mod = f[:-len(".lean")]
        out = build / (mod + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        r = subprocess.run(["lake", "env", "lean", "-o", str(out), "-i", str(out.with_suffix(".ilean")), f],
                           cwd=ROOT, capture_output=True, text=True, env=LEAN_ENV, timeout=3600)
        if r.returncode != 0 or "error" in r.stdout:
            fail(f"{f}: Lean errors\n{r.stdout[-3000:]}{r.stderr[-2000:]}")
        for n in names:
            full = f"{ns}.{n}"
            hits = re.findall(r"'" + re.escape(full) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                              r.stdout)
            if len(hits) != 1:
                fail(f"{full}: missing or duplicate axiom report")
            used = {a.strip() for a in hits[0].split(",") if a.strip()}
            if not used <= ALLOWED:
                fail(f"{full}: axioms {used - ALLOWED}")
        count += len(names)
        print(f"  lean ok: {f} ({len(names)} theorems)")
    return count


def main():
    m = json.loads(MANIFEST.read_text())
    if "--update-hashes" in sys.argv:
        m["hashes"] = {p: sha(p) for p in m["hashes"]}
        MANIFEST.write_text(json.dumps(m, indent=1, ensure_ascii=False) + "\n")
        print("hashes updated")
        return 0

    print("1. Lean (case chain)")
    n_case = check_lean(m)
    print("   Lean (supporting results outside the SC-01 chain)")
    n_supp = check_lean(m, "supporting_lean")

    print("2. hashes")
    bad = [p for p, h in m["hashes"].items() if sha(p) != h]
    if bad:
        fail(f"hash mismatch: {bad} (run with --update-hashes after an intended change)")
    print(f"  {len(m['hashes'])} files match")

    print("3. gateway differential test")
    r = subprocess.run([sys.executable, "difftest_core.py"], cwd=ROOT / "gateway", capture_output=True, text=True,
                       env=LEAN_ENV, timeout=3600)
    print("  " + r.stdout.strip().replace("\n", "\n  "))
    if r.returncode != 0:
        fail("differential test mismatches")

    print("4. usefulness receipt")
    receipt = m["evidence"]["usefulness_receipt"]
    r = subprocess.run([sys.executable, "gateway/scenario/check_receipt.py", receipt], cwd=ROOT, capture_output=True,
                       text=True, timeout=1800)
    if r.returncode != 0:
        fail("receipt verifier failed\n" + r.stdout[-2000:] + r.stderr[-2000:])
    summ = json.loads((ROOT / receipt).read_text())["summary"]
    for cond in ["baseline", "mediated"]:
        s = summ[cond]
        if (s["completed_lifetimes"], s["lifetimes"]) != (64, 64) or Fraction(s["completion_interval"][0]) != Fraction(93382, 100000):
            fail(f"{cond}: receipt does not match the Lean-certified 64/64 endpoint 93382/100000")
    print("  receipt verified; both conditions 64/64, endpoint 93382/100000 = Lean endpoint64")

    print("5. side-certificate hypothesis vs measured evidence")
    cache_path = m["evidence"]["side_channel_receipt"]
    r = subprocess.run([sys.executable, "gateway/scenario/check_cache_receipt.py", cache_path], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        fail("cache receipt verifier failed (it recomputes the endpoint and source hashes)\n" + r.stdout[-2000:] + r.stderr[-2000:])
    print("  " + r.stdout.strip())
    cache = json.loads((ROOT / cache_path).read_text())
    p_lo = Fraction(cache["one_sided_lower"])
    threshold = Fraction(65536, 59049)
    refuted = 2 * p_lo > threshold
    print(f"  single-bit recovery {cache['correct']}/{cache['n']}, one-sided lower {p_lo} "
          f"-> certificate mass >= {float(2 * p_lo):.3f} vs allowed {float(threshold):.4f}: "
          f"{'REFUTED in this harness' if refuted else 'not refuted (this does not establish the hypothesis)'}")

    print("\nAssumptions (provenance | testability | status):")
    rows = []
    for a in m["assumptions"]:
        status = a["status"]
        if a["id"] == "side_certificate" and refuted:
            status = "REFUTED_IN_CURRENT_HARNESS"
        rows.append(dict(id=a["id"], status=status, provenance=a.get("provenance"), testability=a.get("testability"),
                         refutation=a.get("refutation")))
        print(f"  [{status}] {a['id']} ({a.get('provenance')} | {a.get('testability')}): {a['text']}")
        ref = a.get("refutation")
        if ref:
            print(f"      refuted by: {ref['statistic']}; lemma: {ref['lemma']}; experiment: {ref['experiment']}")
        if a.get("adaptive_form"):
            print(f"      adaptive form: {a['adaptive_form']}")
    untestable = [x["id"] for x in rows if x["testability"] == "not_testable_in_harness"]
    open_testable = [x["id"] for x in rows if x["testability"] == "refutable_by_measurement"
                     and x["status"] not in ("REFUTED_IN_CURRENT_HARNESS",)]
    verdict = "HYPOTHESIS_REFUTED" if refuted else "CONDITIONAL"

    print("\nSUMMARY")
    print(f"  proofs:         PASS ({n_case} case + {n_supp} supporting theorems; standard axioms; model-only, not red-teamed)")
    print(f"  bindings:       PASS ({len(m['hashes'])} file hashes)")
    print("  correspondence: TESTED, NOT PROVED (Python/Lean difftest)")
    print("  evidence:       usefulness receipt VALID; cache-probe receipt VALID")
    if refuted:
        print("  applicability:  NOT APPLICABLE to this harness: side_certificate is refuted by measured evidence")
    else:
        print("  applicability:  no hypothesis refuted by the recorded evidence (not the same as established)")
    print("  conditional model bound: P(exact recovery of a uniform 32-bit secret) <= 2^-16 IF every hypothesis holds;")
    print(f"     premises no measurement in this harness can test: {', '.join(untestable)}")
    print(f"     premises testable but not yet refuted: {', '.join(open_testable) or 'none'}")
    print(f"  usefulness (model): a condition with completion <= 9/10 passes the gate w.p. <= 1/80 IF lifetimes are independent")
    print(f"\nVERDICT: {verdict}" + (" (the safety conjunct does not apply to the current harness)" if refuted else "")
          + ". This output is not a safety certificate.")
    if "--json" in sys.argv:
        out = Path(sys.argv[sys.argv.index("--json") + 1])
        out.write_text(json.dumps(dict(verdict=verdict, proofs="PASS", bindings="PASS", correspondence="TESTED_NOT_PROVED",
                                       evidence="VALID", side_certificate_mass_lower=str(2 * p_lo),
                                       side_certificate_allowed=str(threshold), assumptions=rows,
                                       untestable=untestable, open_testable=open_testable), indent=1) + "\n")
    return 3 if refuted else 0


if __name__ == "__main__":
    sys.exit(main())
