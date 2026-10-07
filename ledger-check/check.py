#!/usr/bin/env python3
"""Re-check the ledger proofs against the frozen ledger statements.

For each CID this assembles exactly what the ledger's Lean gate assembled:

    import Mathlib
    <statement of each transitive dependency, dependencies first>
    namespace PLDep_<dep>      -- once per dependency, after its statement
    open PL_<dep>
    <gated proof of the dependency>
    end PLDep_<dep>
    <statement of the CID>              (ledger/<CAMPAIGN>.lean, defines PL_<CID>.Claim and PL_<CID>.Witness)
    namespace PLProof_<CID>
    open PL_<CID>
    <proof of the CID>                  (proofs/<CID>.lean, defines `claim` and `witness`)
    end PLProof_<CID>
    theorem gate_claim : PL_<CID>.Claim := PLProof_<CID>.claim
    theorem gate_witness : PL_<CID>.Witness := PLProof_<CID>.witness
    #print axioms gate_claim
    #print axioms gate_witness

and runs `lake env lean` on it inside a Mathlib v4.35.0-rc3 project (this directory by default). A CID passes when
Lean exits 0 with no errors and no `sorry`, the proof and statement contain none of the gate's banned tokens, and both
final theorems depend only on the standard axioms propext, Classical.choice and Quot.sound.

The original gate differs only in naming (a random nonce in the proof namespace and the final theorem name) and in
checking `claim` and `witness` in two separate runs.

Usage:
    python3 check.py UMSURVF1 UMPROTF1        # selected CIDs
    python3 check.py --all                    # every CID, one Lean process at a time
    python3 check.py --emit out/ UMCERTF1     # only write the assembled file(s), do not run Lean
Options:
    --project DIR   Lake project with Mathlib v4.35.0-rc3 built (default: $LEDGER_CHECK_PROJECT or this directory)
    --lake PATH     lake executable (default: `lake` on PATH, else ~/.elan/bin/lake)
    --keep DIR      keep the assembled .lean files in DIR
    --timeout SEC   per-CID timeout (default 3600)
"""
from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

# CID -> campaign (statement file ledger/<campaign>.lean) and declared dependencies (as recorded in the ledger).
CAMPAIGN = {
    "UMHSF1": "UMHS", "UMSURVF1": "UMSURV", "UMPROTF1": "UMPROT", "UMSTRATF1": "UMSTRAT",
    "UMNOGOF1": "UMNOGO", "CANONF1": "CANON", "SANDBOXF1": "SANDBOX", "SANDBOX2F1": "SANDBOX2",
    "UMLOWERF1": "UMLOWER", "UMUSEF1": "UMUSE", "UMDEFERF1": "UMDEFER", "UMCERTF1": "UMCERT",
    "UMADAPTF1": "UMADAPT",
}
DEPS = {
    "UMHSF1": [], "UMSURVF1": [], "UMPROTF1": ["UMHSF1", "UMSURVF1"], "UMSTRATF1": ["UMPROTF1"],
    "UMNOGOF1": ["UMPROTF1"], "CANONF1": [], "SANDBOXF1": [], "SANDBOX2F1": ["SANDBOXF1"],
    "UMLOWERF1": ["UMPROTF1"], "UMUSEF1": ["UMPROTF1", "UMSTRATF1"], "UMDEFERF1": ["UMPROTF1"],
    "UMCERTF1": ["UMPROTF1", "UMSTRATF1"], "UMADAPTF1": ["UMLOWERF1"],
}
ORDER = list(CAMPAIGN)  # a valid dependency order

OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# The gate's banned-token list (scanned on RAW text, comments included).
BANNED = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bnative_decide\b", r"\bimplemented_by\b",
    r"\bextern\b", r"\bunsafe\b", r"\bopaque\b", r"\bpartial\b", r"#exit\b", r"#eval\b",
    r"#print\b", r"#check_failure\b", r"\brun_cmd\b", r"\brun_tac\b", r"\brun_elab\b",
    r"\belab\b", r"\belab_rules\b", r"\bmacro\b", r"\bmacro_rules\b", r"\bsyntax\b",
    r"\bnotation\b", r"\binfix[lr]?\b", r"\bprefix\b", r"\bpostfix\b", r"^\s*import\b",
    r"\binitialize\b", r"\bbuiltin_initialize\b", r"ofReduceBool", r"ofReduceNat",
    r"skipKernelTC", r"\bLean\.(Elab|Meta|Environment|Kernel|addDecl)", r"\baddDecl\b",
    r"\bdecide\s*:=\s*true", r"\bcsimp\b", r"\bdeclare_syntax_cat\b", r"\bnamespace\s+PL_",
    r"\bend\s+PL", r"\bset_option\s+(?!maxHeartbeats\s+\d+\b|maxRecDepth\s+\d+\b|"
    r"synthInstance\.maxHeartbeats\s+\d+\b)",
]
# statements open their own PL_ namespace, so the PL patterns do not apply to them
BANNED_STATEMENT = [b for b in BANNED if "PL" not in b]


def scan(src: str, patterns) -> list[str]:
    return [p for p in patterns if re.search(p, src, flags=re.M)]


def statement(cid: str) -> str:
    return (REPO / "ledger" / f"{CAMPAIGN[cid]}.lean").read_text()


def proof(cid: str) -> str:
    return (REPO / "proofs" / f"{cid}.lean").read_text()


def dep_closure(deps: list[str]) -> list[str]:
    """Transitive dependencies, dependencies first, without duplicates (the gate's order)."""
    order: list[str] = []
    seen: set[str] = set()

    def visit(d: str, path: tuple[str, ...] = ()) -> None:
        if d in path:
            raise SystemExit(f"dependency cycle through {d}")
        if d in seen:
            return
        for e in DEPS[d]:
            visit(e, path + (d,))
        seen.add(d)
        order.append(d)

    for d in deps:
        visit(d)
    return order


def assemble(cid: str) -> str:
    parts = ["import Mathlib"]
    for d in dep_closure(DEPS[cid]):
        parts.append(statement(d))
        parts.append(f"namespace PLDep_{d}\nopen PL_{d}\n{proof(d)}\nend PLDep_{d}")
    parts += [
        statement(cid),
        f"namespace PLProof_{cid}",
        f"open PL_{cid}",
        proof(cid),
        f"end PLProof_{cid}",
        f"theorem gate_claim : PL_{cid}.Claim := PLProof_{cid}.claim",
        f"theorem gate_witness : PL_{cid}.Witness := PLProof_{cid}.witness",
        "#print axioms gate_claim",
        "#print axioms gate_witness",
        "",
    ]
    return "\n".join(parts)


def find_lake(explicit: str | None) -> str:
    if explicit:
        return explicit
    on_path = shutil.which("lake")
    if on_path:
        return on_path
    fallback = Path.home() / ".elan" / "bin" / "lake"
    if fallback.exists():
        return str(fallback)
    raise SystemExit("lake not found: install elan or pass --lake")


def axioms_of(out: str, name: str) -> tuple[set[str] | None, str]:
    lines = [l for l in out.splitlines() if l.startswith(f"'{name}'")]
    if len(lines) != 1:
        return None, f"expected one axiom report for {name}, got {len(lines)}"
    line = lines[0]
    if "does not depend on any axioms" in line:
        return set(), ""
    # the axiom list may wrap onto following lines; join until the closing bracket
    idx = out.index(line)
    m = re.search(r"depends on axioms: \[(.*?)\]", out[idx:], flags=re.S)
    if not m:
        return None, f"could not parse axiom report for {name}"
    return {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}, ""


def check(cid: str, project: Path, lake: str, keep: Path | None, timeout: int) -> tuple[bool, str]:
    stmt, prf = statement(cid), proof(cid)
    bad = scan(prf, BANNED)
    if bad:
        return False, f"banned tokens in proof: {bad}"
    bad = scan(stmt, BANNED_STATEMENT)
    if bad:
        return False, f"banned tokens in statement: {bad}"
    text = assemble(cid)
    tmpdir = Path(tempfile.mkdtemp(prefix="ledger-check-"))
    f = tmpdir / f"Check_{cid}.lean"
    f.write_text(text)
    if keep:
        keep.mkdir(parents=True, exist_ok=True)
        (keep / f.name).write_text(text)
    t0 = time.time()
    try:
        r = subprocess.run([lake, "env", "lean", str(f)], cwd=project, capture_output=True,
                           text=True, timeout=timeout)
        rc, out = r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        rc, out = 124, "TIMEOUT"
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)
    dt = time.time() - t0
    if rc != 0:
        return False, f"lean exit {rc} ({dt:.0f}s)\n{out[-4000:]}"
    if re.search(r"\berror\b", out) or "declaration uses 'sorry'" in out:
        return False, f"errors ({dt:.0f}s)\n{out[-4000:]}"
    report = []
    for name in ("gate_claim", "gate_witness"):
        ax, err = axioms_of(out, name)
        if ax is None:
            return False, f"{err}\n{out[-4000:]}"
        if not ax <= OK_AXIOMS:
            return False, f"{name} uses non-standard axioms: {sorted(ax - OK_AXIOMS)}"
        report.append(f"{name}: [{', '.join(sorted(ax))}]")
    return True, f"{dt:.0f}s; " + "; ".join(report)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cids", nargs="*", help="CIDs to check (see CAMPAIGN in this file)")
    ap.add_argument("--all", action="store_true", help="check every CID")
    ap.add_argument("--project", default=os.environ.get("LEDGER_CHECK_PROJECT", str(HERE)))
    ap.add_argument("--lake", default=None)
    ap.add_argument("--keep", default=None, help="directory to keep the assembled files in")
    ap.add_argument("--emit", default=None, help="only write the assembled files to this directory")
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    cids = ORDER if a.all else a.cids
    unknown = [c for c in cids if c not in CAMPAIGN]
    if not cids or unknown:
        ap.error(f"give CIDs from {ORDER} or --all" + (f" (unknown: {unknown})" if unknown else ""))
    if a.emit:
        out = Path(a.emit)
        out.mkdir(parents=True, exist_ok=True)
        for cid in cids:
            (out / f"Check_{cid}.lean").write_text(assemble(cid))
            print(f"wrote {out / f'Check_{cid}.lean'}")
        return 0
    project, lake = Path(a.project).resolve(), find_lake(a.lake)
    keep = Path(a.keep) if a.keep else None
    failed = 0
    for cid in cids:  # sequential: one Lean process at a time
        deps = dep_closure(DEPS[cid])
        print(f"{cid} (ledger/{CAMPAIGN[cid]}.lean; deps: {', '.join(deps) or 'none'}) ...", flush=True)
        ok, msg = check(cid, project, lake, keep, a.timeout)
        failed += not ok
        print(f"  {'PASS' if ok else 'FAIL'}: {msg}", flush=True)
    print(f"{len(cids) - failed}/{len(cids)} passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
