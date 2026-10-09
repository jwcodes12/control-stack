#!/usr/bin/env python3
"""new_scenario: scaffold a scenario that follows the SC-26 pattern end to end (stdlib only).

    python3 tools/new_scenario.py SC-29 spec.json            # write the skeleton
    python3 tools/new_scenario.py SC-29 spec.json --dry-run  # print the plan, write nothing
    python3 tools/new_scenario.py --example-spec > spec.json # a complete example spec

Given a small JSON spec (bad_event, roles, ops, checks, effect) it writes, and NEVER overwrites:

  ControlStack/Scenarios/SC<nn><Name>.lean   St / Op / Roles / Checks / full / Sound / init / step / run / legal / sys,
                                             compiling, with `step` = identity (a placeholder that proves nothing) and
                                             commented TODO blocks for Inv, Good, the safety theorem, HALT, spec and
                                             one necessity witness per check (pattern: SC26Transaction.lean)
  scenarios/SC-<nn>/harness/model.py         executable mirror of the Lean definitions, `op_from_row`, `to_lean`
  scenarios/SC-<nn>/harness/check_trace.py   (a) model replay, (b) model = world, (c) c-rule registry, mutation
                                             self-test that requires every rule to fire; fail-closed (INCOMPLETE)
  scenarios/SC-<nn>/harness/run_sc<nn>.py    receipt conventions of run_sc26.py / run_sc28.py: --out must not exist,
                                             dry label by default, `--label evidence` refused unless the prereg is
                                             frozen (not a DRAFT), its sha256 is in env, --out is under evidence/,
                                             pinned hashes in prereg section 7 match, and the pinned files are clean
  prereg/SC<nn>-DRAFT.md                     every section of prereg/SC26-TRANSACTION-GATE-v2.md, a pinned-artifacts
                                             table, and the SC-26 review lessons as a checklist

Every target is checked before anything is written; if any exists (or another ControlStack/Scenarios/SC<nn>*.lean
exists: namespace clash), nothing is written. Exit codes: 0 ok, 1 invalid spec or refusal, 2 usage.
Nothing generated is evidence. The skeleton compiles so that the next edit starts from a building file.
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ID_RE = re.compile(r"SC-(\d{2,3})\Z")
NAME_RE = re.compile(r"[A-Z][A-Za-z0-9]*\Z")
IDENT_RE = re.compile(r"[a-z][A-Za-z0-9]*\Z")
FINDING_RE = re.compile(r"c[0-9]+\Z")
TYPES = {"Nat": ("ℕ", "int"), "Bool": ("Bool", "bool"), "Payload": ("Payload", "Payload")}
LEAN_KW = {"at", "by", "do", "else", "end", "for", "fun", "have", "if", "import", "in", "let", "match", "mut",
           "namespace", "open", "return", "section", "show", "then", "theorem", "lemma", "def", "where", "with",
           "from", "structure", "inductive", "class", "instance", "deriving", "variable", "example", "abbrev",
           "calc", "unless", "universe", "local", "private", "protected", "partial", "unsafe", "macro", "syntax",
           "set_option", "attribute", "noncomputable", "opaque", "axiom", "extends", "Type", "Prop", "Sort",
           "true", "false", "this", "next", "rfl", "sorry", "init", "full", "step", "run", "legal", "sys", "spec"}
PY_KW = {"False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue", "def", "del",
         "elif", "else", "except", "finally", "for", "from", "global", "if", "import", "in", "is", "lambda",
         "nonlocal", "not", "or", "pass", "raise", "return", "try", "while", "with", "yield", "match", "case"}
# op names become module-level functions in model.py: never shadow its definitions or common builtins
RESERVED_OP = {"guard", "inv", "good", "sound", "payload_from", "op_from_row", "op_to_lean", "to_lean",
               "roles_to_lean", "checks_to_lean", "id", "type", "print", "len", "sorted", "set", "any", "all", "sum",
               "map", "tuple", "list", "dict", "str", "int", "bool", "iter", "range", "open", "min", "max", "zip",
               "repr", "isinstance", "getattr", "object", "super", "annotations"}
RESERVED_FIELD = {"count", "index", "halted"}  # NamedTuple methods; St's own fields
RESERVED_PAYLOAD = {"key", "caller", "t"}  # columns of effect rows next to the payload fields
SPEC_KEYS = {"id", "name", "title", "bad_event", "roles", "ops", "checks", "effect", "rules"}
REQUIRED = SPEC_KEYS - {"id", "rules"}

EXAMPLE = {
    "id": "SC-99",
    "name": "Demo",
    "title": "Agent triggers a paid external action without an exact approval",
    "bad_event": "An effect entry exists whose payload no approver (other than its requester) approved.",
    "roles": ["agents", "approvers", "admins"],
    "effect": {"name": "ledger", "doc": "the external system's append-only effect log, keyed by idempotency key",
               "payload": {"dest": "Nat", "amount": "Nat"}},
    "ops": [
        {"name": "request", "doc": "an agent requests an effect", "args": {"caller": "Nat", "p": "Payload"}},
        {"name": "approve", "doc": "an approver approves request `id` with payload `p`",
         "args": {"caller": "Nat", "id": "Nat", "p": "Payload"}},
        {"name": "deliver", "doc": "the gate sends an approved request to the external system",
         "args": {"id": "Nat"}},
        {"name": "directCall", "doc": "a direct call to the external system by `caller`",
         "args": {"caller": "Nat", "key": "Nat", "p": "Payload"}}
    ],
    "checks": [
        {"name": "payload", "doc": "approval binds the exact payload", "sound": True,
         "finding": "c2", "finding_doc": "every effect has an approver-log entry with the same key and exact payload"},
        {"name": "distinct", "doc": "approver differs from the requester", "sound": True,
         "finding": "c3", "finding_doc": "the approver is not an agent and differs from the requester"},
        {"name": "haltCheck", "doc": "every operation checks the HALT bit", "sound": False,
         "finding": "c4", "finding_doc": "no effect was first sent after the first accepted HALT"},
        {"name": "auth", "doc": "the external system accepts only the gate credential", "sound": True,
         "finding": "c1", "finding_doc": "every effect was performed by the gate credential"}
    ],
    "rules": [{"id": "c5", "doc": "no duplicate idempotency key in the effect log"}]
}


class SpecError(ValueError):
    pass


def need(ok, msg):
    if not ok:
        raise SpecError(msg)


def ident(x, where, extra=frozenset()):
    need(isinstance(x, str) and IDENT_RE.match(x), f"{where}: {x!r} must match [a-z][A-Za-z0-9]*")
    need(x not in LEAN_KW and x not in PY_KW and x not in extra,
         f"{where}: {x!r} is reserved (Lean/Python keyword or a name the skeleton defines)")
    return x


def text(x, where):
    need(isinstance(x, str) and x.strip() and "-/" not in x and "/-" not in x and '"""' not in x,
         f"{where}: expected non-empty text without comment delimiters")
    return x.strip()


def validate(spec, sid):
    need(isinstance(spec, dict), "spec: expected a JSON object")
    extra = spec.keys() - SPEC_KEYS
    need(not extra, f"spec: unknown keys {sorted(extra)}")
    missing = REQUIRED - spec.keys()
    need(not missing, f"spec: missing keys {sorted(missing)}")
    if "id" in spec:
        need(spec["id"] == sid, f"spec id {spec['id']!r} does not match {sid}")
    need(isinstance(spec["name"], str) and NAME_RE.match(spec["name"]), "name: must be CamelCase [A-Z][A-Za-z0-9]*")
    text(spec["title"], "title")
    text(spec["bad_event"], "bad_event")
    roles = spec["roles"]
    need(isinstance(roles, list) and roles, "roles: non-empty list")
    for r in roles:
        ident(r, "roles", RESERVED_FIELD)
        need(r != "gate", "roles: 'gate' is the gate credential and is added automatically")
    need(len(set(roles)) == len(roles), "roles: duplicates")
    need("admins" in roles, "roles: must include 'admins' (who may HALT)")
    eff = spec["effect"]
    need(isinstance(eff, dict) and set(eff) == {"name", "doc", "payload"}, "effect: keys name, doc, payload")
    ident(eff["name"], "effect.name", RESERVED_FIELD)
    text(eff["doc"], "effect.doc")
    need(isinstance(eff["payload"], dict) and eff["payload"], "effect.payload: non-empty object field -> type")
    for f, t in eff["payload"].items():
        ident(f, "effect.payload", RESERVED_FIELD | RESERVED_PAYLOAD)
        need(t in ("Nat", "Bool"), f"effect.payload.{f}: type must be Nat or Bool")
    ops = spec["ops"]
    need(isinstance(ops, list) and ops, "ops: non-empty list")
    names = []
    for i, o in enumerate(ops):
        need(isinstance(o, dict) and set(o) == {"name", "doc", "args"}, f"ops[{i}]: keys name, doc, args")
        names.append(ident(o["name"], f"ops[{i}].name", RESERVED_OP))
        text(o["doc"], f"ops[{i}].doc")
        need(isinstance(o["args"], dict), f"ops[{i}].args: object arg -> type")
        for a, t in o["args"].items():
            ident(a, f"ops[{i}].args")
            need(t in TYPES, f"ops[{i}].args.{a}: type must be one of {sorted(TYPES)}")
        if o["name"] == "halt":
            need(o["args"] == {"caller": "Nat"}, "ops: a user-supplied halt must have exactly args {caller: Nat}")
    need(len(set(names)) == len(names), "ops: duplicate names")
    checks = spec["checks"]
    need(isinstance(checks, list) and checks, "checks: non-empty list (one per enforced check; each needs a control)")
    cn, fd = [], []
    for i, c in enumerate(checks):
        need(isinstance(c, dict) and set(c) == {"name", "doc", "sound", "finding", "finding_doc"},
             f"checks[{i}]: keys name, doc, sound, finding, finding_doc")
        cn.append(ident(c["name"], f"checks[{i}].name", RESERVED_FIELD))
        text(c["doc"], f"checks[{i}].doc")
        need(isinstance(c["sound"], bool), f"checks[{i}].sound: boolean")
        need(isinstance(c["finding"], str) and FINDING_RE.match(c["finding"]), f"checks[{i}].finding: c<number>")
        fd.append(c["finding"])
        text(c["finding_doc"], f"checks[{i}].finding_doc")
    need(len(set(cn)) == len(cn), "checks: duplicate names")
    need(len(set(fd)) == len(fd), "checks: each control must fire its OWN specific finding (duplicate finding id)")
    rules = spec.get("rules", [])
    need(isinstance(rules, list), "rules: list")
    for i, r in enumerate(rules):
        need(isinstance(r, dict) and set(r) == {"id", "doc"}, f"rules[{i}]: keys id, doc")
        need(isinstance(r["id"], str) and FINDING_RE.match(r["id"]), f"rules[{i}].id: c<number>")
        need(r["id"] not in fd, f"rules[{i}].id: {r['id']} already used by a check")
        fd.append(r["id"])
        text(r["doc"], f"rules[{i}].doc")
    need(len(set(fd)) == len(fd), "rules: duplicate ids")
    out = json.loads(json.dumps(spec))
    if "halt" not in names:
        out["ops"].append({"name": "halt", "doc": "trusted HALT by an admin (added by the generator)",
                           "args": {"caller": "Nat"}})
    out.setdefault("rules", [])
    return out


# ---------------------------------------------------------------- Lean

def lean_skeleton(spec, nn, gen_note):
    eff, P = spec["effect"], spec["effect"]["payload"]
    ns = f"ControlStack.SC{nn}"
    role_fields = "\n".join(f"  {r} : List ℕ" for r in spec["roles"])
    pay_fields = "\n".join(f"  {f} : {TYPES[t][0]}" for f, t in P.items())
    op_lines = []
    for o in spec["ops"]:
        args = "".join(f" ({a} : {TYPES[t][0]})" for a, t in o["args"].items())
        op_lines.append(f"  /-- {o['doc']} -/\n  | {o['name']}{args}")
    check_fields = "\n".join(f"  /-- {c['doc']} (control finding {c['finding']}) -/\n  {c['name']} : Bool"
                             for c in spec["checks"])
    full = ", ".join(f"{c['name']} := true" for c in spec["checks"])
    sound = [c for c in spec["checks"] if c["sound"]]
    sound_fields = "\n".join(f"  {c['name']} : C.{c['name']} = true" for c in sound)
    sound_proof = "⟨" + ", ".join("rfl" for _ in sound) + "⟩"
    arms = []
    for o in spec["ops"]:
        pats = " _" * len(o["args"])
        argdoc = ", ".join(o["args"]) or "no arguments"
        arms.append(f"  | .{o['name']}{pats} => s  -- TODO ({argdoc}): {o['doc']}")
    roles_lit = "⟨" + ", ".join(f"[{i + 1}]" for i in range(len(spec["roles"]))) + ", 9⟩"
    witnesses = "\n\n".join(
        f"""/-- without `{c['name']}`, a concrete trace reaches the bad event -/
theorem no_{c['name']}_breaks :
    let s := run R0 {{ full with {c['name']} := false }} init [/- TODO: concrete trace -/]
    ¬ Good R0 s := by
  sorry""" for c in spec["checks"])
    return f"""/-
SC-{nn}: {spec['title']}

SKELETON generated by tools/new_scenario.py ({gen_note}). It compiles and proves NOTHING: `step` is the identity
placeholder, `legal` admits every operation, and Inv / Good / the safety theorem / HALT / spec / witnesses are
commented TODO blocks below. Pattern: `ControlStack/Scenarios/SC26Transaction.lean` (one JOINT shared-state
transition system per effect).

Bad event: {spec['bad_event']}
Effect: {eff['doc']}. The effect log is `St.{eff['name']}` (idempotency key, payload); `Good` must constrain it.

Before any claim (lessons of reviews/sc26-2026-10-09/opus-review-summary.md):
- state every premise in the docstrings (credential separation, role disjointness, receiver idempotency);
- say WHICH check gives exactly-once (gate nonce vs receiver dedup) and prove a witness for each check;
- model in-flight effects at HALT (send vs arrive) instead of an atomic delivery;
- prove a non-vacuity theorem (the honest trace produces the effect);
- keep `model.py` a line-by-line mirror and difftest it against `#eval`.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace {ns}

open ControlStack.Gate

/-- the effect payload -/
structure Payload where
{pay_fields}
deriving DecidableEq, Repr

/-- trusted role assignment (by OS identity); `gate` is the gate's own credential, the only one the external
system accepts -/
structure Roles where
{role_fields}
  gate : ℕ

structure St where
  /-- next request id (also the idempotency key) -/
  next : ℕ
  /-- absorbing HALT bit -/
  halted : Bool
  /-- {eff['doc']}: (key, payload) -/
  {eff['name']} : List (ℕ × Payload)
  -- TODO: the gate's own records (requests, approvals, reservations, spend, in-flight `net`), as in SC-26
deriving DecidableEq, Repr

inductive Op where
{chr(10).join(op_lines)}
deriving DecidableEq, Repr

/-- which checks the implementation performs; `full` is the deployed configuration -/
structure Checks where
{check_fields}
deriving DecidableEq, Repr

def full : Checks := {{ {full} }}

/-- the checks the SAFETY property needs. TODO: justify every exclusion with a theorem (cf. SC-26 `good_without_nonce`). -/
structure Sound (C : Checks) : Prop where
{sound_fields}

theorem sound_full : Sound full := {sound_proof}

def init : St := {{ next := 0, halted := false, {eff['name']} := [] }}

/-- PLACEHOLDER: the identity on every operation. Replace each arm with the real transition; every check in
`Checks` must be consulted somewhere (otherwise its control cannot fire). -/
def step (_R : Roles) (_C : Checks) (s : St) : Op → St
{chr(10).join(arms)}

def run (R : Roles) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R C) s

/-- PLACEHOLDER: untrusted operations never carry the gate's credential (credential separation). Every operation is
currently legal; restrict it as in SC-26 (`| .bankCall c _ _ => c ≠ R.gate`). -/
def legal (_R : Roles) : Op → Prop := fun _ => True

/-- the gate as a `Gate.System` over legal operations; its effect log is `St.{eff['name']}` -/
def sys (R : Roles) : System St {{o : Op // legal R o}} (ℕ × Payload) where
  step := fun s o => step R full s o.1
  effects := St.{eff['name']}

/-- witness roles: role i gets UID i+1 (in the order of the spec); the gate credential is 9 -/
def R0 : Roles := {roles_lit}

/-- sanity: the empty trace is the initial state -/
example : run R0 full init [] = init := rfl

/- ## TODO: the invariant and the safety property (see SC26Transaction.lean `Inv`, `Good`, `Inv.good`)

structure Inv (R : Roles) (s : St) : Prop where
  -- one field per fact the proof needs about every reachable state

/-- the safety property: TODO, a predicate on `s.{eff['name']}` that excludes the bad event -/
def Good (R : Roles) (s : St) : Prop := sorry

theorem inv_init (R : Roles) : Inv R init := sorry
theorem step_inv (R : Roles) {{C : Checks}} (hC : Sound C) (s : St) (o : Op) (ho : legal R o) (h : Inv R s) :
    Inv R (step R C s o) := by
  sorry
theorem Inv.good {{R : Roles}} {{s : St}} (h : Inv R s) : Good R s := sorry

/-- **SC-{nn} safety.** After any legal trace from the initial state, `Good` holds. -/
theorem sc{nn}_safe (R : Roles) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : Good R (run R full init ops) := by
  sorry
-/

/- ## TODO: HALT (see SC26Transaction.lean `step_halted`, `halt_freezes`, `inflight_after_halt`)

theorem halt_freezes (R : Roles) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) :
    -- the gate sends nothing new; only messages already in flight may still land
    True := by
  sorry
-/

/- ## TODO: the gate spec (needs `Inv`)

def spec (R : Roles) : Spec (sys R) where
  Inv := Inv R
  ok := fun s e => sorry
  step_inv := fun s o h => step_inv R sound_full s o.1 o.2 h
  log_prefix := fun s o => sorry
  inv_ok := fun _ h e he => sorry
-/

/- ## TODO: non-vacuity and one necessity witness per check (each must FIRE its control's finding)

/-- **Non-vacuity**: the honest trace produces the effect -/
theorem honest_trace_effects : (run R0 full init [/- TODO -/]).{eff['name']} ≠ [] := by decide

{witnesses}
-/

end {ns}
"""


# ---------------------------------------------------------------- model.py

def model_py(spec, nn, lean_rel):
    eff, P = spec["effect"], spec["effect"]["payload"]
    pfields = "\n".join(f"    {f}: {TYPES[t][1]}" for f, t in P.items())
    rfields = "\n".join(f"    {r}: tuple" for r in spec["roles"])
    cfields = "\n".join(f"    {c['name']}: bool" for c in spec["checks"])
    ctor = []
    for o in spec["ops"]:
        params = ", ".join(o["args"])
        items = [f'"{o["name"]}"'] + [f"Payload(*{a})" if t == "Payload" else a for a, t in o["args"].items()]
        ctor.append(f"def {o['name']}({params}): return ({', '.join(items)},)")
    from_row = []
    for o in spec["ops"]:
        vals = ", ".join(f"payload_from(a[\"{x}\"])" if t == "Payload" else f"a[\"{x}\"]" for x, t in o["args"].items())
        from_row.append(f"    if tag == \"{o['name']}\":\n        return {o['name']}({vals})")
    to_lean = []
    for o in spec["ops"]:
        parts = "".join(" {" + ("_payload_lean" if t == "Payload" else ("_bool_lean" if t == "Bool" else "str"))
                        + f"(o[{i + 1}])}}" for i, (a, t) in enumerate(o["args"].items()))
        to_lean.append(f"    if tag == \"{o['name']}\":\n        return f\"Op.{o['name']}{parts}\"")
    pay_lean = ", ".join("{" + ("_bool_lean" if t == "Bool" else "str") + f"(p.{f})}}" for f, t in P.items())
    sound = " and ".join(f"C.{c['name']}" for c in spec["checks"] if c["sound"]) or "True"
    roles_lean = ", ".join("{l(R." + r + ")}" for r in spec["roles"])
    tags = ", ".join(f'"{o["name"]}"' for o in spec["ops"])
    step_arms = "\n".join(f"    if tag == \"{o['name']}\":\n        return s  # TODO: mirror the Lean arm for "
                          f"`{o['name']}`" for o in spec["ops"])
    return f'''"""Executable transliteration of the Lean model `ControlStack.SC{nn}` ({lean_rel}).

SKELETON generated by tools/new_scenario.py. Every definition here must mirror the Lean definition of the same name,
line by line: `Payload`, `Roles`, `St`, the `Op` constructors, `Checks`/`FULL`, `INIT`, `step`, `run`, `legal`, and
(once written in Lean) `inv`, `good`, `sound`. States are immutable tuples. `guard` is NOT a Lean definition: it is
the condition under which `step` takes its non-identity branch, so the trace checker can compare the runtime's
accept/refuse decision with the model's. Unwritten parts raise NotImplementedError so nothing passes by default.
A Lean `#eval` differential test (pattern: scenarios/SC-26/harness/lean_difftest.py) must link this file to Lean.
"""
from __future__ import annotations

from typing import NamedTuple

OPS = ({tags},)


class Payload(NamedTuple):
{pfields}


class Roles(NamedTuple):
{rfields}
    gate: int


class St(NamedTuple):
    next: int
    halted: bool
    {eff['name']}: tuple  # of (key, Payload)


class Checks(NamedTuple):
{cfields}


FULL = Checks({", ".join("True" for _ in spec["checks"])})
INIT = St(0, False, ())


# Op constructors: plain tuples tagged by the Lean constructor name.
{chr(10).join(ctor)}


def payload_from(d) -> Payload:
    """a Payload from a dict (trace/effect rows) or a sequence"""
    if isinstance(d, dict):
        return Payload(**{{k: d[k] for k in Payload._fields}})
    return Payload(*d)


def op_from_row(tag, a):
    """rebuild an Op from a runtime trace row: `tag` = constructor name, `a` = dict of named arguments"""
{chr(10).join(from_row)}
    raise ValueError(f"unknown op {{tag!r}}")


def step(R: Roles, C: Checks, s: St, o) -> St:
    """PLACEHOLDER mirroring the Lean placeholder: the identity on every operation"""
    tag = o[0]
{step_arms}
    raise ValueError(f"unknown op {{o!r}}")


def run(R, C, s, ops):
    for o in ops:
        s = step(R, C, s, o)
    return s


def legal(R: Roles, o) -> bool:
    """PLACEHOLDER mirroring Lean `legal` (every operation legal); restrict it in both places"""
    return True


def guard(R: Roles, C: Checks, s: St, o) -> bool:
    """True iff `step` takes its non-identity branch. TODO once `step` is real."""
    raise NotImplementedError("guard: write it when step is written")


def inv(R: Roles, s: St) -> list:
    """the list of violated `Inv` fields (empty iff `Inv R s`). TODO once Lean `Inv` exists."""
    raise NotImplementedError("inv: mirror Lean Inv field by field")


def good(R: Roles, s: St) -> bool:
    """Lean `Good`. TODO once it exists."""
    raise NotImplementedError("good: mirror Lean Good")


def sound(C: Checks) -> bool:
    """Lean `Sound C`"""
    return bool({sound})


# ---- rendering for the Lean differential test ----

def _bool_lean(b) -> str:
    return "true" if b else "false"


def _payload_lean(p: Payload) -> str:
    return f"⟨{pay_lean}⟩"


def op_to_lean(o) -> str:
    tag = o[0]
{chr(10).join(to_lean)}
    raise ValueError(o)


def to_lean(ops) -> str:
    return "[" + ", ".join(op_to_lean(o) for o in ops) + "]"


def roles_to_lean(R: Roles) -> str:
    l = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
    return f"(⟨{roles_lean}, {{R.gate}}⟩ : Roles)"


def checks_to_lean(C: Checks) -> str:
    return "{{ " + ", ".join(f"{{k}} := {{_bool_lean(v)}}" for k, v in C._asdict().items()) + " }}"
'''


# ---------------------------------------------------------------- check_trace.py

def check_trace_py(spec, nn):
    eff = spec["effect"]
    regs = []
    for c in spec["checks"]:
        regs.append((c["finding"], c["finding_doc"], c["name"]))
    for r in spec["rules"]:
        regs.append((r["id"], r["doc"], None))
    regs.sort(key=lambda x: int(x[0][1:]))
    rule_defs = "\n\n\n".join(
        f'''@rule({json.dumps(rid)}, {json.dumps(doc)})
def rule_{rid}(data, s_model):
    """{('control for check `' + chk + '` must produce THIS finding. ') if chk else ''}Return a list of finding strings."""
    raise NotImplementedError("{rid}")''' for rid, doc, chk in regs)
    control = ", ".join(f'"{c["name"]}": "{c["finding"]}"' for c in spec["checks"])
    pfields = list(spec["effect"]["payload"])
    return f'''#!/usr/bin/env python3
"""Check one SC-{nn} run directory (written by run_sc{nn}.py) against the Lean model and against independent records.

SKELETON generated by tools/new_scenario.py (pattern: scenarios/SC-26/harness/check_trace.py).

Run directory files (conventions; adapt, but keep them independent of each other):
  config.json   roles (one list per role), gate_uid, disabled_checks (names of `Checks` fields)
  trace.json    the gate's linearization: rows {{seq, op, args: {{name: value}}, accepted}}
  effects.json  the REAL external effect log, read from the external system, not from the gate:
                rows {{key, {", ".join(pfields)}, caller, t}}

(a) MODEL REPLAY: replay the trace through model.py from INIT; at every step the runtime's accept/refuse equals the
    model's `guard`, and `inv` holds.
(b) MODEL = WORLD: the model's final `{eff['name']}` equals the real effect log as a multiset of (key, payload).
(c) INDEPENDENT RECONCILIATION: one rule per finding id (registry below). Each negative control must produce its
    SPECIFIC finding (CONTROL_RULE), and the mutation self-test requires every rule to fire on some mutation.

Fail-closed: an unwritten section or rule makes the verdict INCOMPLETE, never PASS. Exit 0 only for PASS.
"""
import argparse
import copy
from collections import Counter
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model as M  # noqa: E402

RULES = {{}}  # finding id -> (description, function)
# each check's negative control must produce exactly this finding (prereg H5)
CONTROL_RULE = {{{control}}}


def rule(rid, doc):
    def reg(fn):
        assert rid not in RULES, rid
        RULES[rid] = (doc, fn)
        return fn
    return reg


{rule_defs}


def load(run):
    run = Path(run)
    j = lambda n: json.loads((run / n).read_text())
    return dict(config=j("config.json"), trace=j("trace.json"), effects=j("effects.json"))


def roles_of(cfg):
    return M.Roles(*(tuple(cfg[r]) for r in M.Roles._fields[:-1]), cfg["gate_uid"])


def check(data):
    cfg = data["config"]
    R = roles_of(cfg)
    C = M.FULL._replace(**{{f: False for f in cfg.get("disabled_checks", [])}})
    report = {{"a_replay": [], "b_world": [], "c_reconcile": {{}}, "not_implemented": []}}
    s = M.INIT
    try:  # ---- (a) ----
        for row in data["trace"]:
            o = M.op_from_row(row["op"], row["args"])
            g = M.guard(R, C, s, o)
            if bool(row["accepted"]) != g:
                report["a_replay"].append(f"accept mismatch at #{{row['seq']}}: runtime={{bool(row['accepted'])}} "
                                          f"model={{g}} op={{o}}")
            s = M.step(R, C, s, o)
            for v in M.inv(R, s):
                report["a_replay"].append(f"Inv.{{v[0]}} fails after #{{row['seq']}}: {{v[1]}}")
                break
    except NotImplementedError as e:
        report["not_implemented"].append(f"(a) {{e}}")
    # ---- (b) ----
    world = sorted((e["key"], tuple(M.payload_from(e))) for e in data["effects"])
    modl = sorted((k, tuple(p)) for k, p in s.{eff['name']})
    if world != modl:
        cw, cm = Counter(world), Counter(modl)
        report["b_world"].append({{"model_only": sorted((cm - cw).elements()),
                                  "world_only": sorted((cw - cm).elements())}})
    # ---- (c) ----
    for rid, (doc, fn) in RULES.items():
        try:
            found = fn(data, s)
        except NotImplementedError:
            report["not_implemented"].append(f"(c) {{rid}}")
            continue
        if found:
            report["c_reconcile"][rid] = list(found)
    bad = report["a_replay"] or report["b_world"] or report["c_reconcile"]
    report["verdict"] = "FAIL" if bad else ("INCOMPLETE" if report["not_implemented"] else "PASS")
    return report


# name -> (rule id it must trigger, mutation of a passing run's data). TODO: at least one per rule.
MUTATIONS = {{}}


def self_test(run):
    base = load(run)
    r0 = check(base)
    out = {{"base_verdict": r0["verdict"], "mutations": {{}}}}
    uncovered = sorted(set(RULES) - {{rid for rid, _ in MUTATIONS.values()}})
    if r0["verdict"] != "PASS" or uncovered:
        out["verdict"] = "FAIL"
        out["why"] = ("self-test needs a passing run" if r0["verdict"] != "PASS" else
                      f"rules that no mutation can fire: {{uncovered}}")
        return out
    for name, (rid, mut) in MUTATIONS.items():
        d = copy.deepcopy(base)
        mut(d)
        r = check(d)
        out["mutations"][name] = {{"expected": rid, "fired": sorted(r["c_reconcile"])}}
    out["verdict"] = "PASS" if all(m["expected"] in m["fired"] for m in out["mutations"].values()) else "FAIL"
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("run")
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    rep = self_test(a.run) if a.self_test else check(load(a.run))
    print(json.dumps(rep, indent=2, default=str))
    return 0 if rep["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
'''


# ---------------------------------------------------------------- run_scNN.py

def run_py(spec, nn, lean_rel, prereg_rel):
    controls = ", ".join(f'"{c["name"]}"' for c in spec["checks"])
    return f'''#!/usr/bin/env python3
"""SC-{nn} harness runner. SKELETON generated by tools/new_scenario.py; conventions copied from
scenarios/SC-26/harness/run_sc26.py and scenarios/SC-28/harness/run_sc28.py.

Phases (each on a FRESH stack; receipts go to --out, which must not exist):
  attacks    : scripted adversary against the full checks; pass iff every attack has its expected outcome AND
               check_trace.py passes on the phase's run directory.
  controls   : for each check in CONTROLS, a fresh stack with ONLY that check disabled (env SC{nn}_NEGATIVE_CONTROL=1),
               the same battery, and the requirement that check_trace reports that check's SPECIFIC finding
               (check_trace.CONTROL_RULE).
  usefulness : the preregistered honest task, with crash injections at every enumerated crash window.
  baseline   : the same honest task without the gate (reported, not gated).

Labels: the default label is `dry-run` (development; never cited as evidence). `--label evidence` is refused unless
  1. the preregistration is frozen: PREREG is not a *-DRAFT.md file;
  2. env SC{nn}_PREREG_SHA256 equals the sha256 of PREREG;
  3. --out is under scenarios/SC-{nn}/evidence/ and does not exist;
  4. every hash in PREREG section 7 (pinned artifacts) equals the current file;
  5. git reports the pinned files, the harness and PREREG unmodified (committed before the run).
Every phase not yet written raises NotImplementedError, which is recorded as ERROR: the verdict is never PASS by default.
"""
import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True  # never leave root-owned __pycache__ in the repo
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
SCENARIO = "SC-{nn}"
PREREG = REPO / "{prereg_rel}"  # rename at freeze (e.g. prereg/SC{nn}-<NAME>-v1.md) and update this line
LEAN_MODEL = REPO / "{lean_rel}"
EVIDENCE_DIR = REPO / "scenarios/SC-{nn}/evidence"
ENV_SHA = "SC{nn}_PREREG_SHA256"
ENV_NEG = "SC{nn}_NEGATIVE_CONTROL"
CONTROLS = [{controls}]
REQUIRE_ROOT = False  # TODO: True when principals run under distinct numeric UIDs (as in SC-26 and SC-28)
PHASES = ["attacks", "controls", "usefulness", "baseline"]
PIN_ROW = re.compile(r"^\\|\\s*`([^`]+)`\\s*\\|\\s*`([0-9a-f]{{64}})`\\s*\\|\\s*$")


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-c", "safe.directory=%s" % REPO, "-C", str(REPO)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def git_info():
    return {{"commit": git("rev-parse", "HEAD"), "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
            "dirty": bool(git("status", "--porcelain")), "status": git("status", "--porcelain")[:4000]}}


def pinned(prereg_text):
    """(path, sha256) rows of the prereg's pinned-artifacts table"""
    return [m.groups() for m in map(PIN_ROW.match, prereg_text.splitlines()) if m]


def pin_report():
    if not PREREG.exists():
        return {{"ok": False, "why": "no prereg"}}
    rows = pinned(PREREG.read_text())
    bad = []
    for path, want in rows:
        f = REPO / path
        got = sha(f) if f.is_file() else None
        if got != want:
            bad.append({{"path": path, "pinned": want, "current": got}})
    return {{"ok": bool(rows) and not bad, "rows": len(rows), "mismatches": bad}}


def evidence_refusal(out):
    """None if an evidence-labelled run may proceed, else the reason (fail-closed)."""
    if PREREG.name.endswith("-DRAFT.md") or not PREREG.exists():
        return "prereg is a DRAFT (or missing): freeze it under a final name first"
    if os.environ.get(ENV_SHA) != sha(PREREG):
        return "env %s must equal sha256 of %s" % (ENV_SHA, PREREG.relative_to(REPO))
    if EVIDENCE_DIR.resolve() not in out.resolve().parents:
        return "--label evidence requires --out under %s" % EVIDENCE_DIR
    pr = pin_report()
    if not pr["ok"]:
        return "pinned artifacts do not match prereg section 7: %s" % json.dumps(pr)[:800]
    paths = [p for p, _ in pinned(PREREG.read_text())] + [str(PREREG.relative_to(REPO))]
    st = git("status", "--porcelain", "--", *paths)
    if st:
        return "pinned files and prereg must be committed and unmodified: " + st[:400]
    return None


def phase_attacks(out):
    raise NotImplementedError("attacks: write the scripted adversary; run check_trace.py on the phase directory")


def phase_controls(out):
    # for each check: fresh stack with env ENV_NEG=1 and only that check disabled; require
    # check_trace.CONTROL_RULE[check] in the reconciliation findings, and the model replay to reproduce the world.
    raise NotImplementedError("controls")


def phase_usefulness(out):
    raise NotImplementedError("usefulness: honest task + crash windows, floor from the prereg")


def phase_baseline(out):
    raise NotImplementedError("baseline")


def main(argv=None):
    ap = argparse.ArgumentParser(description="SC-{nn} harness runner (skeleton)")
    ap.add_argument("--out", type=Path, required=True, help="receipt directory (must not exist)")
    ap.add_argument("--phase", action="append", choices=PHASES)
    ap.add_argument("--label", default="", choices=["", "dry", "evidence"],
                    help="'evidence' only with a frozen prereg, its sha256 in env, --out under evidence/")
    a = ap.parse_args(argv)
    if REQUIRE_ROOT and os.geteuid() != 0:
        raise SystemExit("root required (each principal runs under its own UID)")
    if a.label == "evidence":
        why = evidence_refusal(a.out)
        if why:
            raise SystemExit("refusing evidence label: " + why)
    if a.out.exists():
        raise SystemExit("refusing to overwrite existing receipt directory %s" % a.out)
    phases = a.phase or PHASES
    a.out.mkdir(parents=True)
    receipt = {{"scenario": SCENARIO, "label": a.label if a.label == "evidence" else "dry-run",
               "prereg": str(PREREG.relative_to(REPO)), "prereg_sha256": sha(PREREG) if PREREG.exists() else None,
               "prereg_sha256_env": os.environ.get(ENV_SHA), "pins": pin_report(),
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "git": git_info(), "python": sys.version, "platform": platform.platform(), "argv": sys.argv,
               "harness_sha256": {{f.name: sha(f) for f in sorted(HERE.glob("*.py"))}},
               "lean_model_sha256": sha(LEAN_MODEL) if LEAN_MODEL.exists() else None,
               "phases": {{}}}}
    fns = {{"attacks": phase_attacks, "controls": phase_controls, "usefulness": phase_usefulness,
           "baseline": phase_baseline}}
    for ph in phases:
        t0 = time.monotonic()
        try:
            receipt["phases"][ph] = fns[ph](a.out / ph)
        except Exception as e:  # recorded, never hidden
            receipt["phases"][ph] = {{"verdict": "ERROR", "error": repr(e)}}
        receipt["phases"][ph]["wall_s"] = round(time.monotonic() - t0, 1)
        print(ph, json.dumps(receipt["phases"][ph])[:600], flush=True)
    gated = [p for p in phases if p != "baseline"]
    receipt["verdict"] = "PASS" if gated and all(receipt["phases"][p].get("verdict") == "PASS" for p in gated) \\
        else "FAIL"
    receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    (a.out / "receipt.json").write_text(json.dumps(receipt, indent=1))
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if uid and gid:  # receipts stay owned by the invoking user, as in run_sc28.py
        for root, dirs, files in os.walk(str(a.out)):
            for n in [root] + [os.path.join(root, f) for f in dirs + files]:
                os.chown(n, int(uid), int(gid))
    print("VERDICT", receipt["verdict"])
    return 0 if receipt["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
'''


# ---------------------------------------------------------------- prereg

def prereg_md(spec, nn, lean_rel, harness_rel, prereg_rel, today):
    name = spec["name"].upper()
    controls = "\n".join(f"| {c['name']} | {c['finding']}: {c['finding_doc']} |" for c in spec["checks"])
    rules = "\n".join(f"  - **{rid}:** {doc}" for rid, doc in sorted(
        [(c["finding"], c["finding_doc"]) for c in spec["checks"]] + [(r["id"], r["doc"]) for r in spec["rules"]],
        key=lambda x: int(x[0][1:])))
    pins = "\n".join(f"| `{p}` | `PENDING` |" for p in [
        lean_rel, "ControlStack/Core/Gate.lean", f"{harness_rel}/model.py", f"{harness_rel}/check_trace.py",
        f"{harness_rel}/run_sc{nn}.py", f"{harness_rel}/lean_difftest.py", f"{harness_rel}/README.md"])
    return f"""# Preregistration DRAFT: SC-{nn} {spec['title']}

**ID:** `PREREG-SC{nn}-{name}-v1` (assign at freeze). **Drafted:** {today} by tools/new_scenario.py.
**Status: DRAFT — not frozen, not citable.** The runner refuses an evidence label while this file is named
`*-DRAFT.md`.

**Freeze:** rename to a final name (e.g. `prereg/SC{nn}-{name}-v1.md`), update `PREREG` in
`{harness_rel}/run_sc{nn}.py`, fill §7 with real hashes, and commit together with the model and harness
BEFORE any evidence run. The runner refuses an evidence-labelled run unless env `SC{nn}_PREREG_SHA256` equals this
file's SHA-256, the output directory is under `scenarios/SC-{nn}/evidence/` and does not exist, every §7 hash matches,
and git reports the pinned files unmodified. A mismatch with §7 is a failed run, not a re-run.

## Review lessons checklist (from reviews/sc26-2026-10-09/opus-review-summary.md; tick before freezing)

- [ ] **Pin hashes in the prereg.** §7 lists the SHA-256 of the model, harness and checker; the prereg is frozen only
      after they are committed (SC-26 v1 was frozen before its model was committed, and the model then changed).
- [ ] **Controls must fire their specific finding.** H5 names one finding per disabled check; "something failed" is
      not a pass.
- [ ] **Every reconciliation rule can fire.** The checker's mutation self-test triggers each c-rule at least once
      (SC-26 v1's c3 could not fire).
- [ ] **Dev runs are labelled dry** and go to scratch directories; exactly one evidence run; re-runs only for
      preregistered infrastructure errors, all kept.
- [ ] **The HALT claim matches the model:** effects sent before HALT may land after it (SC-26 `inflight_after_halt`);
      claim "no effect initiated after HALT", not "no effect after HALT".
- [ ] **Say which mechanism gives exactly-once** (gate nonce vs receiver idempotency) and prove it (SC-26 D4).
- [ ] **Docstrings state every premise:** what "approval" and "independent" mean (credential separation, role
      disjointness), not only `legal`.
- [ ] **A necessity witness per check**, including receiver-side checks (SC-26 lacked one for `bankAuth`).
- [ ] **A non-vacuity theorem** (the honest trace produces the effect).
- [ ] **Coverage for the model link (H3):** every Op constructor accepted at least N times; effects actually occur.
- [ ] **Every crash window is enumerated and injected** (SC-26 missed "after intent, before send").
- [ ] **Usefulness fails on any double effect**, not only on missed ones.
- [ ] **Business-level exactly-once** is stated or excluded (SC-26 `same_payload_twice_is_good`, rule c8).
- [ ] **Novelty:** none claimed unless an independent reviewer says otherwise.

## 1. Claim under test and its scope

TODO: state the claim as an observable predicate on the real effect log. Bad event: {spec['bad_event']}

**Model:** `{lean_rel}`. The theorems this run relies on: TODO (e.g. `sc{nn}_safe`, `halt_freezes`).
Its witnesses: TODO (one `no_<check>_breaks` per check: {", ".join(c['name'] for c in spec['checks'])}).

**Premises the run tests but cannot prove:** TODO (credential separation, role disjointness, receiver idempotency,
trust in the kernel, root, interpreter and storage).

**Not tested and not claimed:** TODO (human comprehension, privileged rollback, compromise of trusted code, key
custody, multiple gates, other hosts, usefulness for LLM agents).

## 2. Environment

- **Host:** TODO. Run as `sudo -n /bin/python3 {harness_rel}/run_sc{nn}.py --label evidence --out scenarios/SC-{nn}/evidence/run-1`.
- **Numeric UIDs:** TODO, one per role ({", ".join(spec['roles'])}), plus GATE. No accounts are created.
- **Receipt contents:** commit, dirty status, artifact hashes, interpreter and platform versions, every flag and seed,
  and raw per-sample data.

## 3. Hypotheses and decision rules

Every hypothesis is evaluated once, on the single evidence run. All must pass for an overall PASS.

**H1 Attacks.** TODO: list each attack, its expected outcome, and the pass rule (expected outcome AND H2 on the trace).

**H2 Correspondence and independent reconciliation**, checked on every non-control phase:
- **(a)** each runtime accept or refuse equals the model's guard and `Inv` holds after every replayed step;
- **(b)** the model's final `{spec['effect']['name']}` equals the real effect log, with no duplicate key;
- **(c)** independent reconciliation from records the gate does not control:
{rules}

**H3 Model link.** `lean_difftest.py` at a pinned seed with at least TODO traces: 0 mismatches between `model.py` and
the Lean `#eval`; coverage thresholds TODO.

**H4 Honest usefulness.** Task, crash windows and floor: TODO. Pass needs the floor AND zero double effects.
Baseline without the gate: reported, not gated.

**H5 Controls fire.** Each check in turn is disabled (only with `SC{nn}_NEGATIVE_CONTROL=1`); the control passes only
on its SPECIFIC finding:

| Disabled check | Required finding |
|---|---|
{controls}

The checker's mutation self-test must FAIL every mutation.

## 4. Runs, re-runs and stopping

- **Development runs** use the label `dry` and go to scratch directories only. They are never cited as evidence.
- **The evidence run** uses the label `evidence` and goes to `scenarios/SC-{nn}/evidence/run-1/`. Exactly one.
- **Infrastructure errors:** TODO (which errors allow one further run, to `run-2/`; both kept).
- **Failures:** a hypothesis failure is final for this ID and is recorded as FAILED in the manifest.
- **Stop:** TODO (effects outside the temporary root, escaped processes, ...).

## 5. What a pass licenses

TODO: CONDITIONAL with a kernel-checked model, a trace-checked single-host runtime, fired specific controls and
recorded usefulness. Not deployment assurance; not independent human review.

## 6. What a fail means

The failure is recorded with its raw data and listed as OBSERVED_FAILURE in the manifest. A fix requires a new ID.

## 7. Pinned artifacts (SHA-256 at freeze)

Harness commit: `PENDING`. Fill every row with `sha256sum <path>` after committing; `PENDING` rows make the runner
refuse an evidence label.

| Path | SHA-256 |
|---|---|
{pins}
"""


# ---------------------------------------------------------------- driver

def plan(root: Path, sid: str, spec: dict):
    nn = ID_RE.match(sid).group(1)
    lean_rel = f"ControlStack/Scenarios/SC{nn}{spec['name']}.lean"
    harness_rel = f"scenarios/SC-{nn}/harness"
    prereg_rel = f"prereg/SC{nn}-DRAFT.md"
    today = datetime.date.today().isoformat()
    files = {
        lean_rel: lean_skeleton(spec, nn, f"{today}, spec name {spec['name']}"),
        f"{harness_rel}/model.py": model_py(spec, nn, lean_rel),
        f"{harness_rel}/check_trace.py": check_trace_py(spec, nn),
        f"{harness_rel}/run_sc{nn}.py": run_py(spec, nn, lean_rel, prereg_rel),
        prereg_rel: prereg_md(spec, nn, lean_rel, harness_rel, prereg_rel, today),
    }
    return nn, files


def refusals(root: Path, nn: str, files: dict):
    why = [f"exists: {p}" for p in files if (root / p).exists()]
    scen = root / "ControlStack" / "Scenarios"
    if scen.is_dir():
        for f in sorted(scen.glob(f"SC{nn}*.lean")):
            why.append(f"namespace clash: {f.relative_to(root)} already defines SC-{nn}")
    return why


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("scenario", nargs="?", help="SC-NN")
    ap.add_argument("spec", nargs="?", type=Path, help="JSON spec file")
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--dry-run", action="store_true", help="print the plan, write nothing")
    ap.add_argument("--example-spec", action="store_true", help="print an example spec and exit")
    a = ap.parse_args(argv)
    if a.example_spec:
        print(json.dumps(EXAMPLE, indent=1))
        return 0
    if not a.scenario or not a.spec:
        ap.error("need SC-NN and a spec file (or --example-spec)")
    if not ID_RE.match(a.scenario):
        print(f"invalid scenario id {a.scenario!r} (expected SC-NN)", file=sys.stderr)
        return 1
    try:
        raw = json.loads(a.spec.read_text(encoding="utf-8"))
        spec = validate(raw, a.scenario)
    except (OSError, json.JSONDecodeError, SpecError) as e:
        print(f"INVALID SPEC: {e}", file=sys.stderr)
        return 1
    nn, files = plan(a.root, a.scenario, spec)
    why = refusals(a.root, nn, files)
    if why:
        print("REFUSING (nothing written):\n  " + "\n  ".join(why), file=sys.stderr)
        return 1
    for p in files:
        print(("would write " if a.dry_run else "write ") + p)
    if a.dry_run:
        return 0
    for p, body in files.items():
        f = a.root / p
        f.parent.mkdir(parents=True, exist_ok=True)
        with open(f, "x", encoding="utf-8") as fh:  # "x": never overwrite, even on a race
            fh.write(body)
    lean_rel = next(p for p in files if p.endswith(".lean"))
    mod = lean_rel[:-5].replace("/", ".")
    print(f"""
next steps:
  lake env lean {lean_rel}            # the skeleton must compile before you edit it
  lake build {mod}                    # (not imported by ControlStack.lean; add it there when it is real)
  python3 -c 'import sys; sys.path.insert(0, "scenarios/SC-{nn}/harness"); import model, check_trace'
  edit step/legal/Inv/Good in Lean first, then mirror them in model.py, then write the harness phases""")
    if not (a.root / "scenarios" / f"SC-{nn}" / "manifest.json").exists():
        print(f"  WARNING: scenarios/SC-{nn}/ has no manifest.json; tools/check_scenarios.py scans every folder and "
              f"will fail until the bundle (manifest.json + threat.md, claim.lean, policy.json, correspondence.md, "
              f"result.md, tests/README.md) exists. See scenarios/README.md.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
