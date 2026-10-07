"""Differential test: Python gateway vs the Lean model `GatewayModel.run/deliver` on random adversarial traces.

Raw alphabet R = Fin 8 payload ids: ids 0..3 are valid payloads (schema S = Fin 4), ids 4..7 are invalid payloads.
Actions: ("send", id) or ("other",). Slots = 3. The Lean side evaluates `deliver 3 (run valid 3 trace)` with `#eval`.
"""
import json
import random
import subprocess
import sys
from pathlib import Path

from gateway import Channel, Gateway, NULL, Schema

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
VALID_PAYLOADS = [{"v": i} for i in range(4)]
INVALID_PAYLOADS = [{"v": 9}, {"v": "0"}, {"w": 0}, {"v": 0, "x": 1}]
SCHEMA = Schema((("v", (0, 1, 2, 3)),))


def py_run(trace):
    g = Gateway({"c": Channel("c", SCHEMA, 3)}, budget_bits=16)
    for a in trace:
        if a[0] == "send":
            g.send("c", (VALID_PAYLOADS + INVALID_PAYLOADS)[a[1]])
        else:
            g.act("network")
    g.close()
    return [None if x is NULL else x[0] for x in g.deliver()["c"]]


def lean_run(traces):
    def act(a):
        return f"Act.send ({a[1]} : Fin 8)" if a[0] == "send" else "Act.other"
    body = ",\n  ".join("[" + ", ".join(act(a) for a in t) + "]" for t in traces)
    src = f"""import ControlStack.GatewayModel
open ControlStack.GatewayModel
def valid (r : Fin 8) : Option (Fin 4) := if h : r.val < 4 then some ⟨r.val, h⟩ else none
def traces : List (List (Act (Fin 8))) := [
  {body}]
def fmt (t : List (Act (Fin 8))) : String :=
  ",".intercalate ((List.finRange 3).map (fun i => match deliver 3 (run valid 3 t) i with
    | none => "_" | some v => toString v.val))
#eval IO.println ("\n".intercalate (traces.map fmt))
"""
    f = HERE / "_difftest.lean"
    f.write_text(src)
    out = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, capture_output=True, text=True, timeout=1500)
    f.unlink()
    lines = [l for l in out.stdout.strip().splitlines() if l and all(c in "0123456789_," for c in l)]
    if out.returncode != 0 or len(lines) != len(traces):
        sys.exit("Lean evaluation failed:\n" + out.stdout[-2000:] + out.stderr[-2000:])
    return [[None if x == "_" else int(x) for x in l.split(",")] for l in lines]


def main(n=300, seed=0):
    rng = random.Random(seed)
    traces = []
    for _ in range(n):
        t = []
        for _ in range(rng.randint(0, 6)):
            r = rng.random()
            t.append(("other",) if r < 0.05 else ("send", rng.randrange(8) if r < 0.3 else rng.randrange(4)))
        traces.append(t)
    lean = lean_run(traces)
    py = [py_run(t) for t in traces]
    mism = [i for i in range(n) if lean[i] != py[i]]
    print(f"{n} traces; mismatches: {len(mism)}; blanked: {sum(1 for p in py if p == [None]*3)}; "
          f"full: {sum(1 for p in py if None not in p)}")
    for i in mism[:5]:
        print("MISMATCH", traces[i], "lean", lean[i], "py", py[i])
    return 1 if mism else 0


if __name__ == "__main__":
    raise SystemExit(main())
