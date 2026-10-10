#!/usr/bin/env python3
"""Bounded REAL SQLite/file trace vs independently defined F8 Lean lifecycle.

For each 4-event interleaving, run the SQLite controller and local receiver,
project the persisted and filesystem state after EACH operation, and ask
Lean's kernel to check the same abstract trace projection with `by decide`.
This is a finite, source-scoped differential, NOT a proof of Python, SQLite,
filesystem, OS, clock, credential, or scheduler refinement.
"""
from __future__ import annotations

import itertools
import os
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


def _finset(values):
    return "({" + ", ".join(map(str, sorted(values))) + "} : Finset Nat)" if values \
        else "(∅ : Finset Nat)"


def _expected_state(cap, spent, halted, admitted, published, receipted):
    flag = "true" if halted else "false"
    return ("(⟨" + f"{cap}, {spent}, {flag}, " +
            ", ".join(_finset(items) for items in
                      (admitted, published, receipted)) +
            "⟩ : ControlStack.EffectLifecycle.State)")


_INITIAL = "(⟨2, 0, false, ∅, ∅, ∅⟩ : ControlStack.EffectLifecycle.State)"


def _projection(controller, dbfile, directory, owner):
    snap = controller.state(owner)
    with sqlite3.connect(dbfile) as db:
        releases = {row[0] for row in
                    db.execute("SELECT id FROM releases").fetchall()}
        try:
            receipts = {row[0] for row in
                        db.execute("SELECT release_id FROM delivery_receipts").fetchall()}
        except sqlite3.OperationalError:
            receipts = set()
    published = {int(p.stem) for p in directory.glob("*.body")}
    assert receipts <= published, "receipt before file publication"
    assert len(releases) == snap["releases"], "release-count mismatch"
    assert snap["spent"] <= snap["global_cap"], "global cap exceeded"
    assert snap["global_cap"] == 2, "unexpected policy"
    return _expected_state(2, snap["spent"], snap["halted"],
                           releases, published, receipts)


def _run_case(schedule):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        directory = root / "receiver"
        directory.mkdir(mode=0o700)
        dbfile = root / "gate.db"
        owner = os.geteuid()
        agents = {"agent-a": owner + 26001, "agent-b": owner + 26002}
        reviewer, approver = owner + 26003, owner + 26004
        roles = Principals(frozenset(agents.values()),
                           frozenset({reviewer}), frozenset({approver}),
                           frozenset({owner}))
        c = Controller.bootstrap(dbfile, roles, 2, clock=lambda: 100)
        body = b"bounded-lean-runtime-correspondence"
        digest = c.stage(agents["agent-a"], body)
        c.review(reviewer, digest)
        for name, uid in agents.items():
            lease, nonce = "lease-" + name, "nonce-" + name
            c.issue_lease(owner, lease, uid, 1, 200)
            c.approve(approver, nonce, digest, "fixed-review-label", uid,
                      lease, 150)
        trace = []
        claims = []
        claims.append(([], _projection(c, dbfile, directory, owner)))
        admitted = []
        for event in schedule:
            if event == "halt":
                c.halt(owner)
                trace.append(".halt")
            elif event.startswith("agent-"):
                uid = agents[event]
                nonce, lease = "nonce-" + event, "lease-" + event
                try:
                    rid = c.release(uid, nonce, digest, "fixed-review-label",
                                    lease, record_effect=True)
                except Denied:
                    if not c.state(owner)["halted"]:
                        raise AssertionError("valid request denied without HALT")
                    rid = 100 + list(agents).index(event)
                else:
                    admitted.append(rid)
                trace.append(f".request {uid} {uid} {rid} 1")
            else:
                assert event == "publish"
                for rid in admitted:
                    trace.append(f".publish {rid}")
                    trace.append(f".receipt {rid}")
                    try:
                        name = deliver_record(c, rid, directory)
                    except Denied:
                        if not c.state(owner)["halted"]:
                            raise AssertionError("authorized publication denied")
                    else:
                        assert name == str(rid) + ".body"
                        assert (directory / name).read_bytes() == body
            claims.append((trace.copy(), _projection(c, dbfile, directory, owner)))
        examples = []
        for actions, expected in claims:
            seq = "[" + ", ".join(actions) + "]"
            lhs = "ControlStack.EffectLifecycle.run " + _INITIAL + " " + seq
            examples.append(f"example : ({lhs}) = {expected} := by decide")
        return examples


def main():
    source = ROOT / "reviews" / "family-strengthening" / "EffectLifecycle.lean"
    obligations = []
    for events in itertools.permutations(
            ("agent-a", "agent-b", "publish", "halt")):
        obligations.extend(_run_case(events))
    # Review-scoped Lean source is checked in full, followed by independent
    # runtime-observed projection equations. These cases are finite and do
    # not claim semantic correspondence beyond the tested operations.
    content = source.read_text(encoding="utf-8") + "\n" + "\n".join(obligations) + "\n"
    with tempfile.TemporaryDirectory() as tmp:
        target = Path(tmp) / "JointRuntimeDifferential.lean"
        target.write_text(content, encoding="utf-8")
        run = subprocess.run(["lake", "env", "lean", str(target)],
                             cwd=ROOT, capture_output=True, text=True,
                             timeout=300)
        if run.returncode:
            print(run.stdout[-16000:], file=sys.stderr)
            print(run.stderr[-16000:], file=sys.stderr)
            raise SystemExit(run.returncode)
    print(f"PASS: 24 real-runtime schedules, {len(obligations)} "
          "kernel-checked full-state checkpoints (bounded, not refinement proof)")


if __name__ == "__main__":
    main()
