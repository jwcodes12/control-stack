"""Deterministic Lean gate.  The ONLY path to the 'verified' tier.

Statement files are authored by (untrusted) formulators, red-teamed, then frozen by hash.
They must declare, inside `namespace PL_<cid>`:
    def Claim   : Prop := ...     -- the theorem
    def Witness : Prop := ...     -- non-vacuity: hypotheses jointly satisfiable in a
                                     non-degenerate instance (approved by the red team)
Proof files are authored by (untrusted) provers and must define
    theorem claim   : Claim
    theorem witness : Witness
The gate (not the prover) assembles the check file: frozen statement + proof text inside a
fresh namespace + a final theorem whose name carries a nonce generated *after* the proof
was received, then `#print axioms` on it.  Defences:
  * statement swap      -> final theorem is typed by the frozen `PL_<cid>.Claim`
  * sorry / axioms      -> #print axioms must list only propext/Classical.choice/Quot.sound
  * kernel bypass       -> banned tokens (debug.skipKernelTC, native_decide, extern, ...)
  * forged output/#exit -> banned #-commands, and the nonce'd axiom line must appear once
"""
from __future__ import annotations

import os
import re
import secrets
import subprocess
from pathlib import Path

PROJ = Path(os.environ.get("PL_LEAN_PROJ",
                           Path.home() / "research/alignment-contrib/lean/StabilityDebate"))
LEAN_PATH = f"{Path.home()}/.elan/bin:{os.environ.get('PATH', '')}"
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

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
# statements may not open/close namespaces other than their own and may not use the above
BANNED_STATEMENT = [b for b in BANNED if "PL" not in b]


def _strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    return re.sub(r"--[^\n]*", " ", src)


def scan(src: str, patterns=BANNED) -> list[str]:
    # Scan RAW text: stripping comments/strings with regexes is foolable (e.g. a "--" string
    # literal hides the rest of the line).  Cost: banned words in comments are rejected too.
    return [p for p in patterns if re.search(p, src, flags=re.M)]


GATE_DIR = Path(os.environ.get("PL_GATE_DIR", Path(__file__).resolve().parent.parent / ".gate"))


def run_lean(text: str, tag: str, timeout: int = 900) -> tuple[int, str]:
    # Check files live OUTSIDE the Mathlib project (which provers see read-only), inside the
    # proofledger tree that the sandbox hides, so no prover can read another's proof mid-gate.
    GATE_DIR.mkdir(mode=0o700, exist_ok=True)
    f = GATE_DIR / f"PLGate_{tag}.lean"
    f.write_text(text)
    try:
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=PROJ,
                           capture_output=True, text=True, timeout=timeout,
                           env={**os.environ, "PATH": LEAN_PATH})
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return 124, "TIMEOUT"
    finally:
        f.unlink(missing_ok=True)



def import_header() -> str:
    modules = os.environ.get("PL_IMPORTS", "Mathlib").split()
    if not modules or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", m) for m in modules):
        raise ValueError("PL_IMPORTS must be whitespace-separated Lean module names")
    return "\n".join("import " + m for m in modules)


def check_statement(cid: str, statement: str, dep_statements: list[str] = ()) -> tuple[bool, str]:
    """Statement must compile (after its dependencies' statements only), live in PL_<cid>, and
    define Claim and Witness : Prop.  `dep_statements` lets a stack statement reference
    definitions from the PL_<dep> namespaces of its declared dependencies; the gate later
    includes those dependencies only if they are verified, so an unverified dep fails there."""
    bad = scan(statement, BANNED_STATEMENT)
    if bad:
        return False, f"banned tokens in statement: {bad}"
    body = _strip_comments(statement)
    if not re.search(rf"^\s*namespace\s+PL_{cid}\s*$", body, re.M):
        return False, f"statement must open `namespace PL_{cid}`"
    nonce = secrets.token_hex(4)
    deps = "\n".join(dep_statements)
    text = (f"{import_header()}\n{deps}\n{statement}\n"
            f"example : Prop := PL_{cid}.Claim\nexample : Prop := PL_{cid}.Witness\n")
    rc, out = run_lean(text, f"stmt_{cid}_{nonce}")
    if rc != 0 or re.search(r"\berror\b", out):
        return False, out[-4000:]
    return True, out


GOALS = {"claim": "PL_{cid}.Claim", "witness": "PL_{cid}.Witness",
         "claim_false": "¬ PL_{cid}.Claim"}


def gate(cid: str, statement: str, proof: str, target: str,
         dep_texts: list[str] = (), timeout: int = 900) -> tuple[bool, str]:
    """target in GOALS (the theorem name the prover must define).  Returns (passed, log)."""
    goal_t = GOALS[target].format(cid=cid)
    bad = scan(proof)
    if bad:
        return False, f"REJECT banned tokens in proof: {bad}"
    bad = scan(statement, BANNED_STATEMENT)
    if bad:
        return False, f"REJECT banned tokens in statement: {bad}"
    nonce = secrets.token_hex(6)
    ns = f"PLProof_{cid}_{nonce}"
    final = f"gate_{nonce}"
    text = "\n".join([
        import_header(),
        *dep_texts,
        statement,
        f"namespace {ns}",
        f"open PL_{cid}",
        proof,
        f"end {ns}",
        f"theorem {final} : {goal_t} := {ns}.{target}",
        f"#print axioms {final}",
        "",
    ])
    rc, out = run_lean(text, f"{cid}_{target}_{nonce}", timeout)
    log = out[-8000:]
    if rc != 0:
        return False, f"FAIL lean exit {rc}\n{log}"
    if re.search(r"\berror\b", out) or "declaration uses 'sorry'" in out:
        return False, f"FAIL errors\n{log}"
    lines = [l for l in out.splitlines() if l.startswith(f"'{final}'")]
    if len(lines) != 1:
        return False, f"FAIL expected exactly one axiom report for {final}, got {len(lines)}\n{log}"
    m = re.search(r"depends on axioms: \[(.*)\]", lines[0])
    axioms = {a.strip() for a in m.group(1).split(",")} if m else set()
    if not m and "does not depend on any axioms" not in lines[0]:
        return False, f"FAIL unparseable axiom report\n{log}"
    if axioms - OK_AXIOMS:
        return False, f"FAIL nonstandard axioms {sorted(axioms - OK_AXIOMS)}\n{log}"
    return True, f"PASS {target} axioms={sorted(axioms)}\n{log}"


def extract_lean(text: str) -> str | None:
    """Last ```lean block in a model reply."""
    blocks = re.findall(r"```lean4?\s*\n(.*?)```", text, flags=re.S)
    return blocks[-1].strip() if blocks else None
