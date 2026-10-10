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
    """Independent runtime projection; not a Lean-derived expected value."""
    return {
        "cap": cap,
        "spent": spent,
        "halted": halted,
        "admitted": admitted,
        "published": published,
        "receipted": receipted,
    }


def _projection_obligations(actions, observed):
    """Kernel-check all scalar and finite set data, not a fragile Finset Eq.

    Whole-state `by decide` on derived Finset DecidableEq can get stuck
    reducing proof-transport in Lean 4.34. For each finite set we instead
    check its cardinality and membership for *every* runtime-observed ID.
    These checks jointly entail exact set equality: there cannot be an
    extra model element once all expected elements belong and cardinality
    matches. No native_decide/trustCompiler/unsafe axiom is used.
    """
    seq = "[" + ", ".join(actions) + "]"
    state = "ControlStack.EffectLifecycle.run " + _INITIAL + " " + seq
    clauses = [
        f"({state}).cap = {observed['cap']}",
        f"({state}).spent = {observed['spent']}",
        f"({state}).halted = {'true' if observed['halted'] else 'false'}",
    ]
    for field in ("admitted", "published", "receipted"):
        values = sorted(observed[field])
        clauses.append(f"({state}).{field}.card = {len(values)}")
        for value in values:
            clauses.append(f"{value} ∈ ({state}).{field}")
    return ["example : " + " ∧ ".join(clauses) + " := by decide"]


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
        for actions, observed in claims:
            examples.extend(_projection_obligations(actions, observed))
        return examples



def _run_crash_case(halt_before_recovery):
    """Actually fault the real receiver between durable publication/receipt."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        directory = root / "receiver"
        directory.mkdir(mode=0o700)
        dbfile = root / "gate.db"
        owner = os.geteuid()
        agent, reviewer, approver = owner + 27001, owner + 27002, owner + 27003
        roles = Principals(frozenset({agent}), frozenset({reviewer}),
                           frozenset({approver}), frozenset({owner}))
        c = Controller.bootstrap(dbfile, roles, 2, clock=lambda: 100)
        body = b"exact-crash-recovery-body"
        digest = c.stage(agent, body)
        c.review(reviewer, digest)
        c.issue_lease(owner, "lease", agent, 1, 200)
        c.approve(approver, "nonce", digest, "label", agent, "lease", 150)

        actions = []
        checks = [(actions.copy(), _projection(c, dbfile, directory, owner))]
        rid = c.release(agent, "nonce", digest, "label", "lease",
                        record_effect=True)
        actions.append(f".request {agent} {agent} {rid} 1")
        checks.append((actions.copy(), _projection(c, dbfile, directory, owner)))

        def abort_before_receipt():
            raise RuntimeError("fault after durable file publication")

        try:
            deliver_record(c, rid, directory, after_publish=abort_before_receipt)
        except RuntimeError as exc:
            assert "fault after" in str(exc)
        else:
            raise AssertionError("crash fixture did not interrupt DB receipt")
        assert (directory / f"{rid}.body").read_bytes() == body
        actions.append(f".publish {rid}")
        checks.append((actions.copy(), _projection(c, dbfile, directory, owner)))

        if halt_before_recovery:
            c.halt(owner)
            actions.append(".halt")
            checks.append((actions.copy(), _projection(c, dbfile, directory, owner)))
            try:
                deliver_record(c, rid, directory)
            except Denied:
                pass
            else:
                raise AssertionError("HALT allowed receipt reconciliation")
        else:
            assert deliver_record(c, rid, directory) == f"{rid}.body"
        actions.append(f".receipt {rid}")
        checks.append((actions.copy(), _projection(c, dbfile, directory, owner)))

        examples = []
        for events, observed in checks:
            examples.extend(_projection_obligations(events, observed))
        return examples


def main():
    source = ROOT / "reviews" / "family-strengthening" / "EffectLifecycle.lean"
    obligations = []
    for events in itertools.permutations(
            ("agent-a", "agent-b", "publish", "halt")):
        obligations.extend(_run_case(events))
    obligations.extend(_run_crash_case(halt_before_recovery=False))
    obligations.extend(_run_crash_case(halt_before_recovery=True))
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
    print(f"PASS: 24 real-runtime schedules plus both crash/receipt paths, {len(obligations)} "
          "kernel-checked full-state checkpoints (bounded, not refinement proof)")


if __name__ == "__main__":
    main()
