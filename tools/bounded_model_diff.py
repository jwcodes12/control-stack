#!/usr/bin/env python3
"""Bounded independent Python/Lean *model* differential tests (not runtime refinement).

Shadow transitions are written independently of the Lean source. Python computes
expected observable states; Lean's kernel checks the corresponding finite trace
equations with `by decide`. An erroneous Python acceptance rule produces a
failed Lean obligation. The typed-ingest, complete mediation, credential and
identity assumptions of the Lean models are NOT established by this test.
SC-26 already has a richer independent state oracle: lean_difftest.py.
"""
from __future__ import annotations

import copy
import itertools
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODS = ("SC06OneUse", "SC08Exec", "SC25Audit")


def b(x):
    return "true" if x else "false"


def arr(xs):
    return "[" + ", ".join(xs) + "]"


def norm_traces(alphabet, stories):
    # Exhaust all zero-, one- and two-step traces, plus named causal chains.
    return [()] + [(x,) for x in alphabet] + list(itertools.product(alphabet, repeat=2)) + [tuple(s) for s in stories]


def sc06():
    # Projections are complete for the abstract effects and confirmations;
    # the append-only context store is modeled independently here.
    alphabet = [
        ".ingest 2 1 42", ".ingest 2 2 42", ".confirm 5 3 2 7 0 42",
        ".confirm 6 3 2 7 0 42", ".act 2 7 0 3", ".halt 9",
        ".halt 6", ".act 3 7 0 3",
    ]
    stories = [
        (alphabet[2], alphabet[0], alphabet[4]),  # premature consent
        (alphabet[0], alphabet[2], alphabet[4]),  # useful
        (alphabet[0], alphabet[2], alphabet[4], alphabet[4]),  # replay
        (alphabet[0], alphabet[2], alphabet[5], alphabet[4]),  # halt
        (alphabet[0], alphabet[1], alphabet[2], alphabet[4]),  # own entry
        (alphabet[0], alphabet[2], alphabet[7]),  # wrong reader
        (alphabet[0], ".confirm 5 3 2 7 0 43", alphabet[4]),  # wrong content
        (alphabet[0], alphabet[2], ".confirm 5 4 2 7 0 42",
         alphabet[4], ".act 2 7 0 4"),  # two independent approvals
    ]

    def evaluate(trace):
        entries, confirmations, effects, halted = [], [], [], False
        for ev in trace:
            a = ev.split()
            op = a[0]
            v = list(map(int, a[1:]))
            if op == ".halt":
                if v[0] == 9:
                    halted = True
                continue
            if halted:
                continue
            if op == ".ingest":
                reader, writer, val = v
                entries.insert(0, (len(entries), reader, writer, val))
            elif op == ".confirm":
                issuer, cid, reader, tool, eid, value = v
                if issuer != 5 or any(c[0] == cid for c in confirmations):
                    continue
                if any(e[0] == eid and e[1] == reader and e[2] != reader
                       and e[3] == value for e in entries):
                    confirmations.insert(0, (cid, issuer, reader, tool, eid, value))
            elif op == ".act":
                reader, tool, eid, cid = v
                e = next((x for x in entries if x[0] == eid), None)
                c = next((x for x in confirmations if x[0] == cid), None)
                if (tool == 7 and e is not None and c is not None
                    and e[1] == reader and e[2] != reader
                    and c[1] == 5 and c[2] == reader and c[3] == tool
                    and c[4] == eid and c[5] == e[3]
                    and not any(x[0] == cid for x in effects)):
                    effects.insert(0, (cid, reader, tool, eid, e[3]))
        return confirmations, effects, halted

    decls = []
    for tr in norm_traces(alphabet, stories):
        confirmations, effects, halted = evaluate(tr)
        run = ("ControlStack.SC06OneUse.run ControlStack.SC06OneUse.R0 "
               "ControlStack.SC06OneUse.init " + arr(tr))
        conf = arr(["⟨" + ", ".join(map(str, c)) + "⟩" for c in confirmations])
        eff = arr(["⟨" + ", ".join(map(str, e)) + "⟩" for e in effects])
        decls.append(f"example : ({run}).confirmations = {conf} ∧ ({run}).effects = {eff} ∧ "
                     f"({run}).halted = {b(halted)} := by decide")
    return decls, len(stories)


def sc08():
    alphabet = [
        ".exec 1 none", ".exec 4 (some 5)", ".exec 4 none",
        ".write 2 777", ".exec 4 (some 2)", ".write 3 666",
        ".exec 3 none", ".halt 9",
    ]
    stories = [
        (alphabet[0], alphabet[1]),  # two useful runs
        (alphabet[3], alphabet[4]),  # interpreter source rejected
        (alphabet[5], alphabet[6]),  # injected program rejected
        (alphabet[7], alphabet[0]),  # halt
        (alphabet[1], alphabet[7], alphabet[0]),  # halt after real effect
        (alphabet[3], alphabet[4], alphabet[0]),
        (".halt 3", alphabet[0]),  # unauthorized halt
        (".write 2 10", ".exec 2 none"),  # noexec even if digest allowed
    ]

    def evaluate(trace):
        files = {1: 10, 4: 20, 5: 30}
        ran, halted = [], False
        for ev in trace:
            a = ev.split()
            if a[0] == ".halt":
                if int(a[1]) == 9:
                    halted = True
                continue
            if halted:
                continue
            if a[0] == ".write":
                p, x = map(int, a[1:])
                if p in (2, 3):
                    files[p] = x
            elif a[0] == ".exec":
                p = int(a[1])
                script = None if "none" in ev else int(ev.split("some ")[1].split(")")[0])
                content = files.get(p)
                if (content is None or p == 2 or content not in (10, 20)):
                    continue
                if content == 20:
                    if script is None or files.get(script) not in (30,):
                        continue
                    ran.append((content, files[script]))
                else:
                    ran.append((content, None))
        return ran, halted

    decls = []
    for tr in norm_traces(alphabet, stories):
        ran, halted = evaluate(tr)
        run = ("ControlStack.SC08.run ControlStack.SC08.E0 ControlStack.SC08.full "
               "ControlStack.SC08.s0 " + arr(tr))
        expect = arr([f"({p}, {'none' if s is None else f'(some {s})'})" for p, s in ran])
        decls.append(f"example : ({run}).ran = {expect} ∧ ({run}).halted = {b(halted)} := by decide")
    return decls, len(stories)


def sc25():
    alphabet = [
        ".submit 1 0 150 true", ".audit 2 0 true", ".approve 3 0",
        ".check 0", ".fire 0", ".amend 1 0 151", ".timeout 0",
        ".crash", ".halt 4",
    ]
    stories = [
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[4]), # success
        (alphabet[0], alphabet[1], alphabet[3], alphabet[4]), # missing approval
        (alphabet[0], alphabet[2], alphabet[3], alphabet[4]), # missing audit
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[5], alphabet[4]), # stale check
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[7], alphabet[4]), # crash
        (alphabet[0], alphabet[6], alphabet[1], alphabet[2], alphabet[3], alphabet[4]), # timeout
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[8], alphabet[4]), # halt
        (".submit 1 0 50 false", alphabet[1], alphabet[3], alphabet[4]), # reversible
        (alphabet[0], ".audit 2 0 false", alphabet[2], alphabet[3], alphabet[4]), # fail
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[4], alphabet[4]), # replay
        (alphabet[0], alphabet[1], alphabet[2], alphabet[3], alphabet[5], alphabet[1],
         alphabet[2], alphabet[3], alphabet[4]), # amendment reapproval
    ]

    def evaluate(trace):
        queue, verdicts, approvals = [], [], []
        expired, checked, executed, halted = [], [], [], False
        def item(id_):
            return next((it for it in queue if it[0] == id_), None)
        def valid(it):
            id_, content, _, submitter = it
            if id_ in expired:
                return False
            if not any(v[0] == id_ and v[1] == content and v[2] for v in verdicts):
                return False
            if content >= 100 and not any(ap[0] == id_ and ap[1] == content
                                            and ap[2] != submitter for ap in approvals):
                return False
            return True
        for ev in trace:
            words = ev.split()
            op = words[0]
            args = [int(x) for x in words[1:] if x in ("0", "1", "2", "3", "4", "50", "150", "151")]
            if op == ".halt":
                if args[0] == 4:
                    halted = True
                continue
            if op == ".crash":
                checked = []
                continue
            if halted:
                continue
            if op == ".submit":
                caller, id_, content = args
                declared = words[-1] == "true"
                if caller == 1 and item(id_) is None:
                    queue.insert(0, (id_, content, declared, caller))
            elif op == ".amend":
                caller, id_, content = args
                old = item(id_)
                if caller == 1 and old and id_ not in [x[0] for x in executed]:
                    queue.insert(0, (id_, content, old[2], old[3]))
            elif op == ".audit":
                caller, id_ = args
                if caller == 2 and item(id_):
                    verdicts.append((id_, item(id_)[1], words[-1] == "true"))
            elif op == ".approve":
                caller, id_ = args
                if caller == 3 and item(id_):
                    approvals.append((id_, item(id_)[1], caller))
            elif op == ".timeout":
                id_ = args[0]
                if item(id_) and not any(v[0] == id_ for v in verdicts):
                    expired.append(id_)
            elif op == ".check":
                id_ = args[0]
                if item(id_) and valid(item(id_)):
                    checked.insert(0, id_)
            elif op == ".fire":
                id_ = args[0]
                it = item(id_)
                if (it and id_ in checked and id_ not in [e[0] for e in executed]
                        and valid(it)):
                    executed.append((id_, it[1], it[3], len(verdicts), len(approvals)))
        return executed, expired, halted

    decls = []
    for tr in norm_traces(alphabet, stories):
        executed, expired, halted = evaluate(tr)
        run = ("ControlStack.SC25.run ControlStack.SC25.R0 id ControlStack.SC25.cls0 "
               "ControlStack.SC25.full ControlStack.SC25.init " + arr(tr))
        ex = arr(["⟨" + ", ".join(map(str, e)) + "⟩" for e in executed])
        exp = arr([str(x) for x in expired])
        decls.append(f"example : ({run}).executed = {ex} ∧ ({run}).expired = {exp} ∧ "
                     f"({run}).halted = {b(halted)} := by decide")
    return decls, len(stories)


def main():
    source = ["import ControlStack.Scenarios.SC06OneUse",
              "import ControlStack.Scenarios.SC08Exec",
              "import ControlStack.Scenarios.SC25Audit",
              "set_option maxRecDepth 12000",
              "set_option maxHeartbeats 4000000"]
    counts = {}
    for name, f in (("SC-06", sc06), ("SC-08", sc08), ("SC-25", sc25)):
        equations, targeted = f()
        counts[name] = {"finite_equations": len(equations), "targeted_chains": targeted}
        source.extend(equations)
    with tempfile.TemporaryDirectory(prefix="bounded-lean-") as tmp:
        leanfile = Path(tmp) / "BoundedDiff.lean"
        leanfile.write_text("\n\n".join(source) + "\n")
        p = subprocess.run(["lake", "env", "lean", str(leanfile)], cwd=ROOT,
                           capture_output=True, text=True, timeout=1800)
    print("Bounded model differential equations:", counts, "Lean exit:", p.returncode)
    if p.returncode:
        print(p.stdout[-10000:])
        print(p.stderr[-10000:])
    return p.returncode


if __name__ == "__main__":
    sys.exit(main())
