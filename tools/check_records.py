#!/usr/bin/env python3
"""Mechanical checks for research records in docs/records/*.md.

Each record ends with a fenced block ```json record-index ... ``` listing the Lean declarations and definitions it
cites, the lexical dependencies it claims ("uses"), and its executable files. This checker verifies that
- every cited theorem is in THEOREM-REGISTRY.json (generated from source, drift-checked in CI),
- every cited definition is defined in the named file,
- every claimed use appears in the source text of the using declaration,
- every backticked `Namespace.name` in the record's prose resolves to a cited declaration or definition,
- every executable file exists.
It validates references and lexical structure only. It does not check that the English matches the Lean.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCK = re.compile(r"```json record-index\n(.*?)\n```", re.S)
TOP = re.compile(r"(?m)^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s")
NAMESPACES = ("SplitAudit", "FlagBudget", "Truncation", "ClassAudit", "ReservedAudit", "ReservedRecall", "AuditBudget",
              "Leakage", "Necessity")


def decl_text(path, name):
    src = (ROOT / path).read_text()
    m = re.search(rf"(?m)^(?:noncomputable\s+)?(?:theorem|lemma)\s+{re.escape(name)}\b", src)
    if not m:
        return None
    nxt = TOP.search(src, m.end())
    return src[m.start(): nxt.start() if nxt else len(src)]


def check(record):
    errs = []
    text = record.read_text()
    m = BLOCK.search(text)
    if not m:
        return [f"{record.name}: no record-index block"]
    idx = json.loads(m.group(1))
    registry = {row["key"] for row in json.loads((ROOT / "THEOREM-REGISTRY.json").read_text())}
    names = set()
    for key in idx["declarations"]:
        names.add(key.split("::")[1])
        if key not in registry:
            errs.append(f"declaration not in registry: {key}")
    for key in idx["definitions"]:
        path, name = key.split("::")
        names.add(name)
        if not re.search(rf"(?m)^(?:noncomputable\s+)?(?:def|abbrev)\s+{re.escape(name)}\b", (ROOT / path).read_text()):
            errs.append(f"definition not found: {key}")
    for key, used in idx["uses"].items():
        path, name = key.split("::")
        body = decl_text(path, name)
        if body is None:
            errs.append(f"uses: declaration not found: {key}")
            continue
        for u in used:
            if not re.search(rf"\b{re.escape(u)}\b", body):
                errs.append(f"{name} does not mention {u}")
    prose = text[: m.start()]
    for ns, name in re.findall(r"`(?:ControlStack\.)?(%s)\.([A-Za-z_][A-Za-z_0-9']*)`" % "|".join(NAMESPACES), prose):
        if name != "lean" and name not in names:
            errs.append(f"prose cites `{ns}.{name}` which is not in the record-index")
    for f in idx["executable"]:
        if not (ROOT / f).exists():
            errs.append(f"missing executable file: {f}")
    return [f"{record.name}: {e}" for e in errs]


def main():
    records = sorted((ROOT / "docs/records").glob("*.md"))
    errs = [e for r in records for e in check(r)]
    for e in errs:
        print("FAIL", e)
    print(f"{len(records)} record(s) checked, {len(errs)} problem(s)")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
