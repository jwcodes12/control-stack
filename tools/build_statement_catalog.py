#!/usr/bin/env python3
"""Reproducible source-normalized Lean theorem/lemma catalog.

This is NOT kernel normal form. Inspect full elaborated Lean types separately.
"""
from __future__ import annotations
import argparse
import re
from build_registry import inventory, DECL, ROOT

OUT = ROOT / "LEAN-STATEMENTS-NORMAL-FORM.md"


def header(source, start):
    i, nesting, comment, quote = start, 0, False, False
    while i < len(source) and i < start + 25000:
        pair = source[i:i + 2]
        if comment:
            if source[i] == "\n":
                comment = False
            i += 1
        elif nesting:
            if pair == "/-":
                nesting += 1
                i += 2
            elif pair == "-/":
                nesting -= 1
                i += 2
            else:
                i += 1
        elif quote:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quote = False
                i += 1
            else:
                i += 1
        elif pair == "--":
            comment = True
            i += 2
        elif pair == "/-":
            nesting = 1
            i += 2
        elif source[i] == '"':
            quote = True
            i += 1
        elif pair == ":=":
            text = source[start:i]
            text = re.sub(r"/-[\s\S]*?-/", " ", text)
            text = re.sub(r"--[^\n]*", " ", text)
            return re.sub(r"\s+", " ", text).strip()
        else:
            i += 1
    raise ValueError("missing theorem proof delimiter at " + str(start))


def collect():
    rows = inventory()
    meta = {x[0]: x for x in rows}
    seen = []
    lines = [
        "# All Lean statements — source-normalized review catalog",
        "",
        "Every indexed theorem and lemma is listed with its source statement, "
        "registry metadata and source location; no proof bodies. This is "
        "NOT kernel-elaborated normal form: inherited section variables, "
        "typeclasses, namespace elaboration, coercions and definitions can "
        "hide important premises. Run Lean #print and #print axioms for "
        "authoritative statements. No deployment assurance is implied.",
        "",
        "Indexed declarations: " + str(len(rows)) + "; UNKNOWN adversary: " +
        str(sum(x[3] == "UNKNOWN" for x in rows)) + "; SOURCE_ONLY: " +
        str(sum(x[5] == "SOURCE_ONLY" for x in rows)) + ".",
        "",
    ]
    files = sorted([*(ROOT / "ControlStack").rglob("*.lean"),
                    *(ROOT / "proofs").glob("*.lean"),
                    *(ROOT / "ledger").glob("*.lean")])
    for file in files:
        rel = file.relative_to(ROOT).as_posix()
        source = file.read_text()
        matches = list(DECL.finditer(source))
        if not matches:
            continue
        lines += ["## " + rel, ""]
        counts = {}
        for m in matches:
            name = m.group(1)
            counts[name] = counts.get(name, 0) + 1
            suffix = "" if counts[name] == 1 else "#" + str(counts[name])
            key = rel + "::" + name + suffix
            if key not in meta:
                raise ValueError("unknown theorem declaration " + key)
            row = meta[key]
            line = source.count("\n", 0, m.start()) + 1
            stmt = header(source, m.start())
            if not stmt or len(stmt) > 15000:
                raise ValueError("invalid source statement " + key)
            lines += [
                "### " + str(len(seen) + 1) + ". " + name,
                "",
                "Source: " + rel + ":" + str(line) + " | Family: " + row[1] +
                " | Adversary: " + row[3] + " | Status: " + row[5],
                "",
                "~~~lean",
                stmt,
                "~~~",
                "",
            ]
            seen.append(key)
    if len(seen) != len(rows) or set(seen) != set(meta):
        raise ValueError("incomplete catalog: " + str(len(seen)))
    lines += [
        "## Reviewer obligations",
        "",
        "Check fully elaborated Lean goals and quantified premises; "
        "inspect what Bad, observations, harm, authority and budgets mean; "
        "review model-to-runtime correspondence independently.",
        "",
    ]
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    result = collect()
    if args.check:
        if not OUT.exists() or OUT.read_text() != result:
            raise SystemExit("LEAN-STATEMENTS-NORMAL-FORM.md stale")
        print("Catalog consistent: " + str(len(result)) + " characters")
    else:
        OUT.write_text(result)
        print("Wrote " + str(OUT) + " (" + str(len(result)) + " characters)")


if __name__ == "__main__":
    main()
