"""Differential test: Python gateway vs the multi-channel Lean core `GatewayCore.runG/finalView`.

Two channels: "a" (field v in 0..3, 2 slots) and "b" (field w in 0..2, 1 slot); Lean channel 0 = "a", 1 = "b".
Raw payload ids 0..7: per channel, ids below the schema size are valid payloads, the rest are invalid (wrong value,
wrong type, wrong field, extra field). Events: send to a/b/an unknown channel, a side action (`act`), `close`; events
after close are included so the frozen-snapshot path is exercised. The trusted harness closes at the end of a trace
that never closes. Lean evaluates `finalView (runG valid init trace)` with `#eval`.
"""
import random
import subprocess
import sys
from pathlib import Path

from gateway import NULL, Channel, Gateway, Schema

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SIZES = {"a": 4, "b": 3}
SLOTS = {"a": 2, "b": 1}
FIELD = {"a": "v", "b": "w"}
SCHEMAS = {c: Schema(((FIELD[c], tuple(range(SIZES[c]))),)) for c in SIZES}


def payload(c, rid):
    f = FIELD[c] if c in FIELD else "v"
    if c in SIZES and rid < SIZES[c]:
        return {f: rid}
    return [{f: 9}, {f: str(rid)}, {"zz": 0}, {f: 0, "x": 1}, {f: True}, {f: 1.0}, {f: 7}, {f: -1}][rid % 8]


def py_run(trace):
    g = Gateway({c: Channel(c, SCHEMAS[c], SLOTS[c]) for c in SIZES}, budget_bits=16)
    for e in trace:
        if e[0] == "send":
            g.send(e[1], payload(e[1], e[2]))
        elif e[0] == "other":
            g.act("network")
        else:
            g.close()
    g.close()
    d = g.deliver()
    return [[None if x is NULL else x[0] for x in d[c]] for c in ["a", "b"]]


def lean_ev(e):
    if e[0] == "other":
        return "Ev.other"
    if e[0] == "close":
        return "Ev.close"
    ch = {"a": "(some 0)", "b": "(some 1)"}.get(e[1], "none")
    return f"Ev.send {ch} ({e[2]} : Fin 8)"


def lean_run(traces):
    body = ",\n  ".join("[" + ", ".join(lean_ev(e) for e in t) + "]" for t in traces)
    src = f"""import ControlStack.GatewayCore
open ControlStack.GatewayCore
abbrev Sz : Fin 2 → Type := fun c => Fin (if c.val = 0 then 4 else 3)
abbrev sl : Fin 2 → ℕ := fun c => if c.val = 0 then 2 else 1
def valid (c : Fin 2) (r : Fin 8) : Option (Sz c) :=
  if h : r.val < (if c.val = 0 then 4 else 3) then some ⟨r.val, h⟩ else none
def traces : List (List (Ev 2 (Fin 8))) := [
  {body}]
def fmt (t : List (Ev 2 (Fin 8))) : String :=
  let v := finalView (runG (S := Sz) (slots := sl) valid init t)
  let ch (c : Fin 2) : String := ",".intercalate ((List.finRange (sl c)).map (fun i => match v c i with
    | none => "_" | some x => toString x.val))
  ch 0 ++ "|" ++ ch 1
#eval IO.println ("\\n".intercalate (traces.map fmt))
"""
    f = HERE / "_difftest_core.lean"
    f.write_text(src)
    out = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, capture_output=True, text=True, timeout=1500)
    f.unlink()
    lines = [l for l in out.stdout.strip().splitlines() if l and all(c in "0123456789_,|" for c in l)]
    if out.returncode != 0 or len(lines) != len(traces):
        sys.exit("Lean evaluation failed:\n" + out.stdout[-2000:] + out.stderr[-2000:])
    return [[[None if x == "_" else int(x) for x in part.split(",")] for part in l.split("|")] for l in lines]


def main(n=1000, seed=0, bad=1.0):
    rng = random.Random(seed)
    traces = []
    for _ in range(n):
        t = []
        for _ in range(rng.randint(0, 7)):
            r = rng.random()
            if r < 0.04 * bad:
                t.append(("other",))
            elif r < 0.04 * bad + 0.06:
                t.append(("close",))
            elif r < 0.07 * bad + 0.06:
                t.append(("send", "zz", rng.randrange(8)))
            else:
                c = rng.choice(["a", "b"])
                t.append(("send", c, rng.randrange(8) if rng.random() < 0.2 * bad else rng.randrange(SIZES[c])))
        traces.append(t)
    lean = lean_run(traces)
    py = [py_run(t) for t in traces]
    mism = [i for i in range(n) if lean[i] != py[i]]
    blank = [[None, None], [None]]
    print(f"{n} traces; mismatches: {len(mism)}; blanked: {sum(p == blank for p in py)}; "
          f"with post-close events: {sum(('close',) in t[:-1] for t in traces)}; "
          f"distinct views: {len({str(p) for p in py})}")
    for i in mism[:5]:
        print("MISMATCH", traces[i], "lean", lean[i], "py", py[i])
    return 1 if mism else 0


if __name__ == "__main__":
    # a refusal-heavy mix and a mostly-valid mix (covers the non-blank views)
    raise SystemExit(main(1000, 0, 1.0) | main(1000, 1, 0.1))
