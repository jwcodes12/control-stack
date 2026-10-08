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
Then prints every assumption and its status. Exit 0 means "all checks ran and passed"; the verdict printed is the
case's actual status (CONDITIONAL, or HYPOTHESIS_REFUTED when measured evidence contradicts a hypothesis).
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
    sys.exit(1)


def check_lean(m):
    build = ROOT / ".lake" / "build" / "lib" / "lean"
    for entry in m["lean"]:
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
        print(f"  lean ok: {f} ({len(names)} theorems)")


def main():
    m = json.loads(MANIFEST.read_text())
    if "--update-hashes" in sys.argv:
        m["hashes"] = {p: sha(p) for p in m["hashes"]}
        MANIFEST.write_text(json.dumps(m, indent=1, ensure_ascii=False) + "\n")
        print("hashes updated")
        return 0

    print("1. Lean")
    check_lean(m)

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
    cache = json.loads((ROOT / m["evidence"]["side_channel_receipt"]).read_text())
    p_lo = Fraction(cache["one_sided_lower"])
    threshold = Fraction(65536, 59049)
    refuted = 2 * p_lo > threshold
    print(f"  single-bit recovery {cache['correct']}/{cache['n']}, one-sided lower {p_lo} "
          f"-> certificate mass >= {float(2 * p_lo):.3f} vs allowed {float(threshold):.4f}: "
          f"{'REFUTED in this harness' if refuted else 'not refuted'}")

    print("\nAssumptions:")
    for a in m["assumptions"]:
        status = a["status"]
        if a["id"] == "side_certificate" and refuted:
            status = "REFUTED_IN_CURRENT_HARNESS"
        print(f"  [{status}] {a['id']}: {a['text']}")
    verdict = "HYPOTHESIS_REFUTED (safety conjunct does not apply to the current harness)" if refuted else "CONDITIONAL"
    print(f"\nAll checks passed. Case verdict: {verdict}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
