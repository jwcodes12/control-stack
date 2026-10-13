#!/usr/bin/env python3
"""Prepare a strictly blind two-phase English-to-Lean one-to-one check for a list of headline claims.

  phase A directory: only the English (Says / Under / Does NOT say / Kind, with the Lean file:line stripped), definition-only excerpts of the
                     claims' source files and their project imports (theorems removed, declarations that ARE claims redacted), and an empty
                     back/ directory. No originals, no compiled objects, no toolchain, no earlier results.
  phase B directory: a full checkout copy (made by the caller) receives the hashed back files plus a prompt that tells the second session to
                     compile, freeze repaired hashes, then open the originals and prove the equivalence through the unchanged proofledger gate.

Usage:  python3 tools/blind_one_to_one.py phase-a --claims A.B.name C.D.name ... --out DIR
        python3 tools/blind_one_to_one.py prompts --out DIR --tag g1a        (writes PROMPT-A.md / PROMPT-B.md into DIR)
Claims are fully qualified Lean names listed in docs/lean-english/part-g*.md. Running Sol (`codex exec`) is done by the caller; see
docs/lean-english/one-to-one/blind-v1/ for a completed example and tools/audit_blind_phase.py for the transcript audit.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KEEP_FIELDS = ("Says (plain English)", "Under these hypotheses", "Does NOT say", "Kind")
START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|example|#print|end|namespace|open|import|set_option|variable|section|attribute)\b")


def english_blocks():
    blocks = {}
    for part in sorted((ROOT / "docs/lean-english").glob("part-g[0-7].md")):
        for b in re.split(r"\n(?=### `)", part.read_text()):
            m = re.match(r"### `([^`]+)`\s*—\s*`([^`:]+):(\d+)`", b)
            if m:
                blocks[m.group(1)] = (b, m.group(2), part.name)
    return blocks


def stripped(block):
    head, *fields = block.split("\n- **")
    name = re.match(r"### `([^`]+)`", head).group(1)
    keep = ["- **" + f.rstrip() for f in fields if f.split(":**")[0] in KEEP_FIELDS]
    return f"## `{name}`\n\n" + "\n".join(keep) + "\n"


def split_blocks(text):
    lines, out, cur, kind, pend = text.split("\n"), [], [], None, []
    def flush():
        nonlocal cur, kind
        if cur:
            out.append((kind, "\n".join(cur)))
        cur, kind = [], None
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("/--"):
            flush()
            doc = [l]
            while "-/" not in doc[-1] and i + 1 < len(lines):
                i += 1
                doc.append(lines[i])
            pend = doc
            i += 1
            continue
        m = START.match(l)
        if m:
            flush()
            kind, cur, pend = m.group(1), pend + [l], []
        else:
            if pend and not l.strip():
                cur, kind, pend = pend, kind or "doc", []
            cur.append(l)
        i += 1
    flush()
    return out


def decl_name(block):
    m = re.search(r"\b(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([A-Za-z_][\w.']*)", block)
    return m.group(1) if m else None


def excerpt(path, redact):
    out = []
    # Module-header and other non-docstring block comments often restate the theorems in the authors' words: drop them all.
    text = re.sub(r"/-(?!-)[\s\S]*?-/", "", path.read_text())
    mention = re.compile(r"\b(?:" + "|".join(re.escape(r) for r in sorted(redact)) + r")\b") if redact else None
    for kind, b in split_blocks(text):
        if kind in ("theorem", "lemma", "instance", "example", "#print", "import"):
            continue
        n = decl_name(b)
        if kind in ("def", "abbrev", "structure", "inductive", "class") and n and n.split(".")[-1] in redact:
            out.append(f"-- [redacted declaration: {n}]")
            continue
        if mention:  # a docstring or comment line that names a claim would leak it
            b = "\n".join("-- [line removed: names a claim under test]" if mention.search(l) else l for l in b.split("\n"))
        out.append(b)
    return "\n".join(out)


def project_imports(path, seen, depth):
    found = []
    for m in re.finditer(r"^import (ControlStack(?:\.\w+)+)", path.read_text(), re.M):
        f = ROOT / (m.group(1).replace(".", "/") + ".lean")
        if f.exists() and f not in seen:
            seen.add(f)
            found.append(f)
            if depth > 1:
                found += project_imports(f, seen, depth - 1)
    return found


def phase_a(claims, out):
    blocks = english_blocks()
    missing = [c for c in claims if c not in blocks]
    if missing:
        sys.exit("not in part-g*.md: " + ", ".join(missing))
    out = Path(out)
    (out / "defs").mkdir(parents=True)
    (out / "input").mkdir()
    (out / "back").mkdir()
    redact = {c.split(".")[-1] for c in claims}
    files, seen = [], set()
    for c in claims:
        f = ROOT / blocks[c][1]
        if not f.exists():  # some headers give the path relative to ControlStack/
            f = ROOT / "ControlStack" / blocks[c][1]
        if f not in seen:
            seen.add(f)
            files.append(f)
    for f in list(files):
        files += project_imports(f, seen, 2)
    for f in files:
        name = str(f.relative_to(ROOT / "ControlStack")).replace("/", "__")
        (out / "defs" / (name[:-5] + "_defs.lean")).write_text(
            f"-- EXCERPT of ControlStack/{f.relative_to(ROOT / 'ControlStack')}: definitions only; theorems and redacted declarations removed. Not compilable alone.\n" + excerpt(f, redact) + "\n")
    (out / "input" / "batch.md").write_text("# English statements under test\n\n" + "\n".join(f"### Claim {i + 1}\n" + stripped(blocks[c][0]) for i, c in enumerate(claims)))
    (out / "CLAIMS.txt").write_text("\n".join(f"{i + 1}\t{c}" for i, c in enumerate(claims)) + "\n")
    print(f"phase A directory {out}: {len(claims)} claims, {len(files)} excerpted files")


def prompts(out, tag):
    out = Path(out)
    n = len((out / "CLAIMS.txt").read_text().split("\n")) - 1
    a = f"""You are Sol, doing the STRICTLY BLIND first step of an English-to-Lean one-to-one check for a Lean 4 verification project (a defensive security verifier). The project owner (John) has authorized this run and is giving you this instruction directly.

Working directory: this directory. You may read ONLY `./input/batch.md` and `./defs/*.lean`. You may write ONLY under `./back/`. Do not read or list anything outside this directory, do not use the network or git, and do not look for the original Lean theorems: they are deliberately not here. (`./defs/*.lean` are definition-only excerpts of the project's Lean files with theorems removed and the claim declarations redacted. They are NOT compilable on their own; there is no Lean toolchain here. Be careful with syntax and types; compilation errors will be repaired later by someone else and every repair will be logged and diffed against your hashed text.)

Task. `input/batch.md` holds {n} plain-English statements. For each, write a Lean 4 statement that says EXACTLY what the English says: no more, no less. Read "Says", "Under these hypotheses" and "Does NOT say" as the specification; the last lists over-readings your statement must not make.
- Theorem claims: `def Back_<short_name> : Prop := ...` (closed proposition, universally quantify the arguments). Do not prove anything. Definition claims: `def Back<Name>` with the same parameters.
- Use the project's real names and namespaces as they appear in defs/. If the English cannot be turned into one exact statement (missing data, ambiguity, a notion with no counterpart), write your best effort AND put `NOT_FORMALISABLE: <why>` or `AMBIGUOUS: <readings>` in a `-- NOTE` block above it. Never guess silently.
Files: one per claim, `back/<n>-<short_name>.lean` (n = claim number in batch.md). When all are written run `sha256sum back/*.lean` and write `back/BACK-HASHES.json` as {{"utc": "<now, ISO>", "files": {{"<file>": "<sha256>"}}}}. Do not edit any back file after hashing.
Final answer: for each claim, the file and one or two sentences on what you formalised and any ambiguity. Be plain about uncertainty."""
    b = f"""You are Sol, doing PHASE B of a strictly blind English-to-Lean one-to-one check for a Lean 4 verification project (a defensive security verifier). The project owner (John) has authorized this run and is giving you this instruction directly.

Phase A is finished and was run blind in another directory: a model wrote Lean statements from the English alone, WITHOUT the original theorems, and hashed them. They are in `docs/lean-english/one-to-one/blind-{tag}/back/*.lean` with `BACK-HASHES.json`. The English under test is `docs/lean-english/sol-input/batch-{tag}.md` ({n} claims, numbered as in `docs/lean-english/one-to-one/blind-{tag}/CLAIMS.txt`). Old comparison results have been removed from this checkout; form your own verdicts. Do not read or rely on anything else under `docs/lean-english/` except the input batch, the back files, and the gate helpers `docs/lean-english/one-to-one/run_gate.py`, `leangate_imports.py`, `leangate-imports.patch`.

Working directory: the repository root, which has a built Lean 4 project (`lake env lean` works; Mathlib is available offline; download nothing). Write ONLY under `docs/lean-english/one-to-one/blind-{tag}/`. Never edit `ControlStack/`, never run git.

Per claim:
1. COMPILE the back file as written. Do not rewrite it. Make only the smallest repairs for typing/syntax (an import, a name, a parenthesis) and record each as a diff in `blind-{tag}/compile-fixes/<n>.diff` saying whether it changes meaning. Repaired files go to `blind-{tag}/typed/` and their SHA-256 to `blind-{tag}/typed/HASHES.json` BEFORE you open the original declarations.
2. THEN open the original declaration (find it by name in `ControlStack/`) and compare. State `Back ↔ Orig` pointwise: compare conclusions under the same hypotheses (two closed true theorems are trivially equivalent, so do not use that to manufacture equivalence); for a definition claim prove the pointwise iff. Prove it in Lean or prove each direction separately. Verdicts: `EQUIVALENT` | `ENGLISH_STRONGER` (Back → Orig only) | `ENGLISH_WEAKER` (Orig → Back only) | `DIFFERENT` (counterexample) | `NOT_FORMALISABLE` | `UNDECIDED`. `EQUIVALENT` only if the proof passed the deterministic gate.
3. GATE every proof with proofledger's deterministic gate (see `run_gate.py`: statement file `<cid>.statement.lean` declaring `PL_<cid>.Claim` and `Witness`, proof file defining `theorem claim`/`theorem witness`; imports via `PL_IMPORTS`, which you may extend with the project modules the claims need; project via `PL_LEAN_PROJ`). Copy it to `blind-{tag}/run_gate_blind.py`, change only the output directory, the file glob and PL_IMPORTS, and do NOT weaken the gate's banned-token or axiom checks. Gate the Witness separately. Use ids `b{tag}_<n>`.
4. Be a hostile reader of the English: say whether its "Does NOT say" over-readings are respected, and propose replacement sentences for English that is wrong or ambiguous (text in RESULTS.md only; never edit the part files).
Also write `blind-{tag}/regate.py`: run from the repository root it must re-gate every claim AND witness from the saved statement/proof files (the deterministic gate only, imports/paths as in your run_gate_blind.py), rewrite only the receipts, and exit non-zero if any gate check fails. It must work from a clean state.
Outputs: `blind-{tag}/RESULTS.md` (table: claim, verdict, receipts, note; then "Corrections to the English" and "Ambiguities exposed"), `blind-{tag}/PROGRESS.md` (done / not done / time / what you could not do), and all supporting files. A failed proof, an UNDECIDED or an unfinished claim is a valid outcome; never claim a verdict the gate did not certify. Final answer: the verdict table and the three most important findings."""
    (out / "PROMPT-A.md").write_text(a + "\n")
    (out / "PROMPT-B.md").write_text(b + "\n")
    print("wrote prompts for", tag, "with", n, "claims")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    pa = sub.add_parser("phase-a")
    pa.add_argument("--claims", nargs="+", required=True)
    pa.add_argument("--out", required=True)
    pp = sub.add_parser("prompts")
    pp.add_argument("--out", required=True)
    pp.add_argument("--tag", required=True)
    a = ap.parse_args()
    if a.cmd == "phase-a":
        phase_a(a.claims, a.out)
    else:
        prompts(a.out, a.tag)


if __name__ == "__main__":
    main()
