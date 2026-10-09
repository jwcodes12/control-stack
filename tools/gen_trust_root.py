#!/usr/bin/env python3
"""Regenerate the generated blocks of ControlStack/Core/TrustRoot.lean from the scenario manifests.

Blocks (between `-- BEGIN GENERATED: <name>` and `-- END GENERATED: <name>`):
- `scenarios`: each scenario's normalised premises, from tools/portfolio_ledger.py's `build()`. This is the same
  normalisation as ASSURANCE-LEDGER.md, so the Lean table can no longer drift from it. Premises are listed in
  `Prem` constructor order, and every manifest scenario gets a row.
- `root tables`: the expected values of `scenario_roots_table`, `portfolio_roots` and `root_sharing`. They are
  computed by LEAN: the tool writes a temporary copy of TrustRoot.lean with this block replaced by `#eval`s and runs
  `lake env lean` on it. The theorems are then re-checked by `decide` whenever TrustRoot builds. Python never
  evaluates the dependency graph.
- `summary`: the header bullets that quote those numbers.

Fail closed:
- a normalised premise that `Prem` does not encode, or whose kind differs from `Prem.kind`, is an error. The
  dependency edges (`depsOf`) are a modelling judgement, so a new premise needs a hand-written `Prem` constructor and
  `depsOf` entry;
- a missing or duplicated marker is an error.

Usage: gen_trust_root.py [--check] [--no-lean]
- (default)  rewrite all blocks (needs lake and a built ControlStack.Core.Cert);
- --no-lean  the `scenarios` block only;
- --check    write nothing; exit 1 if a block would change.
Exit codes: 0 = ok / no drift; 1 = drift or error.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TR = Path("ControlStack/Core/TrustRoot.lean")
sys.path.insert(0, str(ROOT / "tools"))
import portfolio_ledger  # noqa: E402

TAG = "(tools/gen_trust_root.py; do not edit by hand)"


class GenError(Exception):
    pass


# ---------------------------------------------------------------- markers

def block_span(text, name):
    begin = f"-- BEGIN GENERATED: {name} {TAG}\n"
    end = f"-- END GENERATED: {name}\n"
    if text.count(begin) != 1 or text.count(end) != 1:
        raise GenError(f"TrustRoot.lean: expected exactly one BEGIN/END marker pair for block {name!r}")
    a = text.index(begin) + len(begin)
    b = text.index(end)
    if b < a:
        raise GenError(f"TrustRoot.lean: END before BEGIN for block {name!r}")
    return a, b


def get_block(text, name):
    a, b = block_span(text, name)
    return text[a:b]


def set_block(text, name, body):
    a, b = block_span(text, name)
    return text[:a] + body + text[b:]


# ---------------------------------------------------------------- Lean source facts

def def_block(text, header):
    m = re.search(re.escape(header) + r"[^\n]*\n((?:[ \t]+\|[^\n]*\n)+)", text)
    if not m:
        raise GenError(f"TrustRoot.lean: cannot find `{header}`")
    return m.group(1)


def prem_facts(text):
    """(constructor order, snake name -> constructor, constructor -> kind) parsed from the Lean source"""
    order = re.findall(r"^\s+\|\s+(\w+)\s*$", def_block(text, "inductive Prem where"), re.M)
    names = dict((snake, ctor) for ctor, snake in
                 re.findall(r'\|\s*\.(\w+)\s*=>\s*"(\w+)"', def_block(text, "def Prem.name")))
    kinds = dict(re.findall(r"\|\s*\.(\w+)\s*=>\s*\.(\w+)", def_block(text, "def Prem.kind")))
    if set(order) != set(names.values()) or set(order) != set(kinds):
        raise GenError("TrustRoot.lean: `Prem`, `Prem.name` and `Prem.kind` do not list the same constructors")
    return order, names, kinds


# ---------------------------------------------------------------- scenarios block

def scenario_premises(root=ROOT, rows=None):
    """scenario number -> set of normalised premise ids, for every manifest scenario"""
    rows = portfolio_ledger.build(root) if rows is None else rows
    out = {int(sid.split("-")[1]): set() for sid in portfolio_ledger.load_manifests(root)}
    for r in rows:
        for sid in r["scenarios"]:
            out.setdefault(int(sid.split("-")[1]), set()).add(r["id"])
    return out, rows


def scenarios_block(text, root=ROOT, rows=None):
    order, names, kinds = prem_facts(text)
    table, rows = scenario_premises(root, rows)
    errors = []
    for r in rows:
        if not r["scenarios"]:
            continue
        if r["id"] not in names:
            errors.append(f"normalised premise {r['id']!r} ({r['kind']}) has no `Prem` constructor; add one, with "
                          f"`Prem.name`, `Prem.kind`, `allPrems` and a `depsOf` entry (a modelling judgement)")
        elif kinds[names[r["id"]]] != r["kind"]:
            errors.append(f"premise {r['id']!r}: ledger kind {r['kind']} but Prem.kind is "
                          f"{kinds[names[r['id']]]}")
    if errors:
        raise GenError("\n".join(errors))
    rank = {c: i for i, c in enumerate(order)}
    lines = []
    for sc in sorted(table):
        ctors = sorted((names[p] for p in table[sc]), key=rank.get)
        lines.append(f"({sc}, [" + ", ".join("." + c for c in ctors) + "])")
    return ("/-- each scenario's normalised premises (generated from tools/portfolio_ledger.py) -/\n"
            "def scenarios : List (ℕ × List Prem) :=\n  [" + ",\n   ".join(lines) + "]\n")


# ---------------------------------------------------------------- root tables via Lean

EVAL = """#eval show IO Unit from do
  for s in scenarios do
    IO.println ("ROOTS " ++ toString s.1 ++ "|" ++ ",".intercalate ((scenarioRoots s.1).map fun r => toString (repr r)))
  for r in allRoots do
    IO.println ("COUNT " ++ toString (repr r) ++ "|" ++
      toString (scenarios.filter (fun s => decide (r ∈ scenarioRoots s.1))).length ++ "|" ++ toString r.technical ++
      "|" ++ r.name)
  for s in scenarios do
    if Prem.modelRuntimeCorrespondence ∈ s.2 then
      IO.println ("REFINE " ++ toString s.1 ++ "|" ++ (refinementOf s.1).getD "")
    for t in scenarioThms s.1 do
      IO.println ("THM " ++ t)
"""


def lean_probe_source(text):
    """TrustRoot.lean with the root-tables block replaced by #evals; trailing #eval/#print lines dropped (they
    refer to the theorems being regenerated)"""
    src = set_block(text, "root tables", EVAL)
    return "\n".join(ln for ln in src.splitlines() if not ln.startswith(("#print", "#eval ControlStack"))) + "\n"


def run_lean_probe(text, root=ROOT, runner=subprocess.run):
    with tempfile.TemporaryDirectory(prefix="gen_trust_root_") as d:
        f = Path(d) / "TrustRootProbe.lean"
        f.write_text(lean_probe_source(text), encoding="utf-8")
        p = runner(["lake", "env", "lean", str(f)], cwd=root, capture_output=True, text=True, timeout=1800)
    out = (p.stdout or "") + (p.stderr or "")
    if p.returncode != 0 or "error" in out:
        raise GenError("Lean probe failed:\n" + "\n".join(out.strip().splitlines()[-20:]))
    extra = {}
    roots, counts = parse_probe(out, extra)
    check_theorem_names(extra.get("thms", set()), root)
    return roots, counts, extra.get("refine", [])


def check_theorem_names(names, root=ROOT):
    """every theorem edge `ControlStack.<…>.<Module>.<decl>` must be a registry declaration `<…>/<Module>.lean::<decl>`
    (fail closed: a renamed or missing theorem is an error)"""
    reg = root / "THEOREM-REGISTRY.json"
    if not names:
        return
    if not reg.is_file():
        raise GenError("THEOREM-REGISTRY.json missing: cannot check theorem edges")
    keys = {e["key"] for e in json.loads(reg.read_text(encoding="utf-8"))}
    missing = []
    for n in sorted(names):
        parts = n.split(".")
        if len(parts) < 3 or not any(k.endswith("/" + parts[-2] + ".lean::" + parts[-1]) for k in keys):
            missing.append(n)
    if missing:
        raise GenError("theorem edges not in THEOREM-REGISTRY.json: " + ", ".join(missing))


def parse_probe(out, extra=None):
    """ROOTS/COUNT lines; REFINE/THM lines go into `extra` (dict) when given"""
    roots, counts = {}, []
    for ln in out.splitlines():
        ln = ln.strip().strip('"')
        if ln.startswith("ROOTS "):
            sc, rs = ln[6:].split("|", 1)
            roots[int(sc)] = [short(r) for r in rs.split(",") if r]
        elif ln.startswith("COUNT "):
            r, n, tech, name = ln[6:].split("|", 3)
            counts.append((short(r), int(n), tech == "true", name))
        elif ln.startswith("REFINE ") and extra is not None:
            sc, t = ln[7:].split("|", 1)
            extra.setdefault("refine", []).append((int(sc), t or None))
        elif ln.startswith("THM ") and extra is not None:
            extra.setdefault("thms", set()).add(ln[4:].strip())
    if not roots or not counts:
        raise GenError("Lean probe printed no ROOTS/COUNT lines")
    return roots, counts


def short(r):
    return r.strip().rsplit(".", 1)[-1]


def plain(name):
    return name.split(" (")[0].replace("_", " ")


def correspondence_block(refine):
    if not refine:
        return ""
    rows = ",\n       ".join(f"({sc}, {'some (refName ' + str(sc) + ' "' + t.rsplit('.', 1)[-1] + '")' if t else 'none'})"
                     for sc, t in refine)
    return (
        "\n/-- **Model–runtime correspondence, per scenario.** For each scenario with that premise, the theorem edge is the\n"
        "scenario's OWN refinement (`none`: it rests on `implementation_conformance` alone). -/\n"
        "theorem correspondence_table :\n"
        "    (scenarios.filter (fun s => decide (Prem.modelRuntimeCorrespondence ∈ s.2))).map\n"
        "      (fun s => (s.1, refinementOf s.1)) =\n"
        f"      [{rows}] := by\n"
        "  decide\n")


def root_tables_block(roots, counts, refine=()):
    n_sc = len(roots)
    rows = [f"({sc}, [" + ", ".join("." + r for r in roots[sc]) + "])" for sc in sorted(roots)]
    all_roots = [c[0] for c in counts]
    used = [c[0] for c in counts if c[1] > 0]
    n_tech = sum(1 for c in counts if c[2])
    top = max(c[1] for c in counts)
    first = next(c for c in counts if c[1] == top)
    tech = sorted((c for c in counts if c[2]), key=lambda c: -c[1])[:2]
    shown = [first] + [c for c in tech if c[0] != first[0]]
    used_lean = "allRoots" if used == all_roots else "[" + ", ".join("." + r for r in used) + "]"
    conj = " ∧\n    ".join(
        f"(scenarios.filter (fun s => decide (Root.{c[0]} ∈ scenarioRoots s.1))).length = {c[1]}" for c in shown)
    return (
        "/-- **The minimal root set of every scenario.** -/\n"
        "theorem scenario_roots_table : scenarios.map (fun s => (s.1, scenarioRoots s.1)) =\n"
        "      [" + ",\n       ".join(rows) + "] := by\n"
        "  decide\n\n"
        "/-- **The whole portfolio** rests on these roots. -/\n"
        "theorem portfolio_roots :\n"
        f"    allRoots.filter (fun r => decide (∃ s ∈ scenarios, r ∈ scenarioRoots s.1)) = {used_lean} ∧\n"
        f"    (allRoots.filter Root.technical).length = {n_tech} := by\n"
        "  decide\n\n"
        + textwrap.fill(f"/-- **Root sharing.** {sharing_sentence(first, tech, n_sc)} -/", width=118,
                        break_on_hyphens=False) + "\n"
        "theorem root_sharing :\n"
        f"    {conj} ∧\n"
        f"    ∀ r ∈ allRoots, (scenarios.filter (fun s => decide (r ∈ scenarioRoots s.1))).length ≤ {top} := by\n"
        "  decide\n" + correspondence_block(list(refine)))


def sharing_sentence(first, tech, n_sc):
    kind = "technical" if first[2] else "RESIDUAL"
    s = f"The most-shared root is the {kind} `{first[3].split(' (')[0]}` ({first[1]} of {n_sc} scenarios)."
    if len(tech) == 2:
        s += (f" The most-shared technical roots are {plain(tech[0][3])} ({tech[0][1]}) and "
              f"{plain(tech[1][3])} ({tech[1][1]}).")
    return s


def summary_block(roots, counts, refine=()):
    n_sc = len(roots)
    used = [c for c in counts if c[1] > 0]
    n_tech = sum(1 for c in used if c[2])
    top = max(c[1] for c in counts)
    first = next(c for c in counts if c[1] == top)
    tech = sorted((c for c in counts if c[2]), key=lambda c: -c[1])[:2]
    which = f"all {len(counts)} roots" if len(used) == len(counts) else f"{len(used)} of the {len(counts)} roots"
    kind = "technical" if first[2] else "residual"
    share = (f"- `root_sharing`: the most-shared root is the {kind} `{first[3].split(' (')[0]}` ({first[1]} of {n_sc} "
             f"scenarios)")
    if len(tech) == 2:
        share += (f"; the most-shared\n  technical roots are {plain(tech[0][3])} ({tech[0][1]}) and "
                  f"{plain(tech[1][3])} ({tech[1][1]})")
    return (f"- `scenario_roots_table`: the root set of each of the {n_sc} scenarios. Dependencies are conjunctive "
            "(every listed dep is\n"
            "  needed), so the reachable root set is the unique minimal set of roots that suffices;\n"
            f"- `portfolio_roots`: the whole portfolio rests on {which}: {n_tech} technical, {len(used) - n_tech} "
            "residual;\n" + share + (";" if refine else ".") + "\n" + refine_summary(list(refine)))


def refine_summary(refine):
    if not refine:
        return ""
    own = ", ".join(f"SC-{sc:02d}" for sc, t in refine if t)
    none = ", ".join(f"SC-{sc:02d}" for sc, t in refine if not t)
    s = f"- `correspondence_table`: model–runtime correspondence is discharged by the scenario's OWN refinement for {own}"
    if none:
        s += f"; {none} rest on implementation_conformance alone"
    return textwrap.fill(s + ".", width=118, subsequent_indent="  ") + "\n"


# ---------------------------------------------------------------- main

def regenerate(text, root=ROOT, lean=True, runner=subprocess.run, rows=None):
    new = set_block(text, "scenarios", scenarios_block(text, root, rows))
    if lean:
        roots, counts, refine = run_lean_probe(new, root, runner)
        new = set_block(new, "root tables", root_tables_block(roots, counts, refine))
        new = set_block(new, "summary", summary_block(roots, counts, refine))
    return new


def main(argv=None, root=ROOT, runner=subprocess.run):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="exit 1 if TrustRoot.lean would change; write nothing")
    ap.add_argument("--no-lean", action="store_true", help="the scenarios block only")
    a = ap.parse_args(argv)
    path = root / TR
    try:
        text = path.read_text(encoding="utf-8")
        new = regenerate(text, root, lean=not a.no_lean, runner=runner)
    except (GenError, portfolio_ledger.LedgerError, OSError, ValueError) as e:
        print(f"gen_trust_root: {e}", file=sys.stderr)
        return 1
    names = ["scenarios"] + ([] if a.no_lean else ["root tables", "summary"])
    changed = [n for n in names if get_block(text, n) != get_block(new, n)]
    if a.check:
        if changed:
            print(f"TrustRoot.lean drift in generated block(s): {', '.join(changed)} "
                  f"(run python3 tools/gen_trust_root.py{' --no-lean' if a.no_lean else ''})", file=sys.stderr)
            return 1
        print(f"TrustRoot.lean generated blocks up to date ({', '.join(names)})")
        return 0
    if changed:
        path.write_text(new, encoding="utf-8")
        print(f"rewrote {TR}: {', '.join(changed)}")
    else:
        print(f"{TR} unchanged")
    return 0


if __name__ == "__main__":
    sys.exit(main())
