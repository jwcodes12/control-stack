#!/usr/bin/env python3
"""Enumerate dependencies from Lean's elaborated environment, not source grep."""
from __future__ import annotations
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs/lean-english"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}

LEAN_PREFIX = r"""
import Lean
import ControlStack
open Lean Elab Command

private def projectClosure (env : Environment) (root : Name) : Array Name × Bool := Id.run do
  let mut visited : NameSet := {}
  let mut pending : List Name := [root]
  let mut output : Array Name := #[]
  for _ in [:200000] do
    match pending with
    | [] => break
    | n :: rest =>
      pending := rest
      unless visited.contains n do
        visited := visited.insert n
        if let some info := env.find? n then
          if n != root && "ControlStack.".isPrefixOf n.toString then
            output := output.push n
          -- Non-project imported libraries cannot depend back on ControlStack.
          -- Restrict project closure to project constants; collectAxioms below
          -- separately computes the full axiom footprint through all imports.
          pending := (info.getUsedConstantsAsSet.toList.filter
            (fun child => "ControlStack.".isPrefixOf child.toString)) ++ pending
  return (output.qsort Name.lt, pending.isEmpty)

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[ROOT_NAMES]
  for root in roots do
    let some info := env.find? root
      | throwError "Missing elaborated declaration: {root}"
    let (closure, complete) := projectClosure env root
    unless complete do
      throwError "Environment dependency closure did not terminate: {root}"
    let direct := (info.getUsedConstantsAsSet.toList.filter
      (fun n => "ControlStack.".isPrefixOf n.toString)).toArray.qsort Name.lt
    let axioms ← collectAxioms root
    let row := Json.mkObj [
      ("lean", toJson root.toString),
      ("direct", toJson (direct.toList.map toString)),
      ("dependencies", toJson (closure.toList.map toString)),
      ("axioms", toJson (axioms.toList.map toString))]
    liftIO <| IO.println ("CSDEP:" ++ row.compress)
"""


def claim_names() -> list[str]:
    names = []
    for path in sorted(OUT.glob("part-g*.md")):
        for line in path.read_text().splitlines():
            match = re.match(r"^### \x60([A-Za-z0-9_.']+)\x60", line)
            if match:
                names.append(match.group(1))
    if len(names) != 187:
        raise ValueError(f"expected 187 claims, got {len(names)}")
    return names


def environment_rows(names: list[str]) -> dict[str, dict]:
    distinct = list(dict.fromkeys(names))
    for name in distinct:
        if not name.startswith("ControlStack."):
            raise ValueError(f"not fully qualified: {name}")
    script_text = LEAN_PREFIX.replace(
        "ROOT_NAMES", ", ".join(chr(96) + n for n in distinct))
    with tempfile.TemporaryDirectory(prefix="lean-dependencies-") as temp:
        script = Path(temp) / "Dependencies.lean"
        script.write_text(script_text)
        process = subprocess.run(
            ["lake", "env", "lean", str(script)], cwd=ROOT,
            text=True, capture_output=True)
        if process.returncode:
            raise RuntimeError("Lean environment extraction failed:\n"
                               + process.stdout[-16000:] + process.stderr[-16000:])
    rows = {}
    for line in process.stdout.splitlines():
        if line.startswith("CSDEP:"):
            row = json.loads(line.removeprefix("CSDEP:"))
            key = row["lean"]
            if key in rows:
                raise ValueError(f"duplicate output: {key}")
            for field in ("direct", "dependencies", "axioms"):
                if not isinstance(row.get(field), list):
                    raise ValueError(f"missing field {field} for {key}")
                row[field] = sorted(set(row[field]))
            if not set(row["direct"]) <= set(row["dependencies"]):
                raise ValueError(f"incomplete project closure for {key}")
            rows[key] = row
    if set(rows) != set(distinct):
        raise ValueError(f"missing: {sorted(set(distinct)-set(rows))}")
    return rows


def render() -> tuple[str, str]:
    names = claim_names()
    resolved = environment_rows(names)
    entries = [
        {"ordinal": i, **resolved[name],
         "axioms_standard": set(resolved[name]["axioms"]) <= ALLOWED}
        for i, name in enumerate(names, 1)
    ]
    unsupported = [(e["ordinal"], e["lean"], e["axioms"])
                   for e in entries if not e["axioms_standard"]]
    if unsupported:
        raise ValueError(f"nonstandard Lean axioms in environment inventory: {unsupported}")
    machine = json.dumps({
        "method": "Lean Environment ConstantInfo transitive closure and collectAxioms",
        "claim_count": len(entries), "claims": entries
    }, indent=2, ensure_ascii=False) + "\n"
    human = [
        "# Lean dependencies for 187 headline claims", "",
        "Generated from elaborated Lean declarations, not source-text grep. "
        "Model-written/model-reviewed; no independent human review.", "",
        f"Claims: {len(entries)} (duplicates retained).", "",
        "The JSON stores direct and transitive project declarations and "
        "the transitive Lean axiom set.", "",
        "| # | Lean name | Direct project deps | Transitive project deps | Axioms | Standard |",
        "|---|---|---:|---:|---|---|"
    ]
    for e in entries:
        ax = ", ".join(e["axioms"]) or "(none)"
        human.append(f"| {e['ordinal']} | {e['lean']} | "
                     f"{len(e['direct'])} | {len(e['dependencies'])} | "
                     f"{ax} | {'yes' if e['axioms_standard'] else 'NO'} |")
    human.extend(["", "Dependencies do not establish runtime correspondence, "
                  "environment truth or English statement fidelity.", ""])
    return machine, "\n".join(human)


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    p.add_argument("--emit-bootstrap", action="store_true")
    args = p.parse_args()
    json_data, md_data = render()
    outputs = {OUT / "DEPENDENCIES.json": json_data,
               OUT / "DEPENDENCIES.md": md_data}
    if args.check:
        for path, content in outputs.items():
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f"stale Lean dependencies: {path}")
        print("Lean dependency indexes consistent: 187 claims")
    else:
        for path, content in outputs.items():
            path.write_text(content)
        print("generated Lean environment dependency indexes: 187 claims")
    if args.emit_bootstrap:
        payload = json.dumps({"json": json_data, "md": md_data},
                             separators=(",", ":"), ensure_ascii=True)
        for i in range(0, len(payload), 12000):
            print(f"CSDEPCHUNK:{i:08d}:{payload[i:i+12000]}")


if __name__ == "__main__":
    main()
