#!/usr/bin/env python3
"""Finite Python/SQLite vs pinned Lean one-nonce delegation differential.

Two complete four-event permutation sets compare both positive and negative
release orderings. This checks observations under simulated SO_PEERCRED UIDs,
not a theorem of host or Python semantic correspondence.
"""
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
from trusted_stack.server import run_one


def observe(c, path, admin):
    snapshot = c.state(admin)
    with sqlite3.connect(path) as db:
        used, = db.execute("SELECT used FROM approvals WHERE nonce='nonce'").fetchone()
        grant = db.execute("SELECT grantor_uid,delegate_uid,revoked FROM delegations WHERE nonce='nonce'").fetchone()
        releases, = db.execute("SELECT COUNT(*) FROM releases").fetchone()
        records, = db.execute("SELECT COUNT(*) FROM effect_records").fetchone()
    assert snapshot["releases"] == releases == records == used
    assert snapshot["spent"] == releases <= 1
    return snapshot, grant, bool(used)


def lean_claim(actions, snap, grant, used, owner, admin):
    init = (f"(⟨1, 0, false, {owner}, {admin}, none, false, false⟩ : "
            "ControlStack.DelegatedAdmission.State)")
    expr = "ControlStack.DelegatedAdmission.run " + init + " [" + ", ".join(actions) + "]"
    bits = [
        f"({expr}).spent = {snap['spent']}",
        f"({expr}).cap = {snap['global_cap']}",
        f"({expr}).halted = {'true' if snap['halted'] else 'false'}",
        f"({expr}).used = {'true' if used else 'false'}",
        f"({expr}).owner = {owner}",
    ]
    if grant is None:
        bits += [f"({expr}).grant = (none : Option Nat)",
                 f"({expr}).revoked = false"]
    else:
        assert grant[0] == owner
        bits += [f"({expr}).grant = (some {grant[1]} : Option Nat)",
                 f"({expr}).revoked = {'true' if grant[2] else 'false'}"]
    return "example : " + " ∧ ".join(bits) + " := by decide"


def run_case(schedule):
    with tempfile.TemporaryDirectory() as root:
        parent = Path(root)
        admin = os.geteuid()
        owner, delegate, reviewer, approver = [admin + i for i in (60001, 60002, 60003, 60004)]
        p = Principals(frozenset({owner, delegate}), frozenset({reviewer}),
                       frozenset({approver}), frozenset({admin}))
        db_path = parent / "state.db"
        c = Controller.bootstrap(db_path, p, 1, clock=lambda: 100)
        data = b"fixed-approved-delegation"
        digest = c.stage(owner, data)
        c.review(reviewer, digest)
        c.issue_lease(admin, "lease", owner, 1, 200)
        c.approve(approver, "nonce", digest, "reviewed", owner, "lease", 150)
        statements = []
        lean_events = []
        snap, grant, used = observe(c, db_path, admin)
        statements.append(lean_claim(lean_events, snap, grant, used, owner, admin))
        for action in schedule:
            if action == "grant":
                req = {"op": "delegate", "nonce": "nonce", "delegate_uid": delegate}
                uid, lean = owner, f".grant {owner} {delegate}"
            elif action == "revoke":
                req = {"op": "revoke_delegation", "nonce": "nonce"}
                uid, lean = owner, f".revoke {owner}"
            elif action == "halt":
                req = {"op": "halt"}
                uid, lean = admin, f".halt {admin}"
            elif action in ("owner_use", "delegate_use"):
                uid = owner if action == "owner_use" else delegate
                req = {"op": "effect_release", "nonce": "nonce",
                       "digest": digest, "destination": "reviewed", "lease_id": "lease"}
                lean = f".use {uid}"
            else:
                raise AssertionError("unknown operation")
            try:
                run_one(c, uid, req)
            except Denied:
                pass
            lean_events.append(lean)
            snap, grant, used = observe(c, db_path, admin)
            statements.append(lean_claim(lean_events, snap, grant, used, owner, admin))
        return statements


def main():
    assertions = []
    for alphabet in (("grant", "delegate_use", "revoke", "halt"),
                     ("grant", "owner_use", "revoke", "halt"),
                     ("grant", "owner_use", "delegate_use", "halt")):
        for schedule in itertools.permutations(alphabet):
            assertions.extend(run_case(schedule))
    source = (ROOT / "reviews" / "family-strengthening" /
              "DelegatedAdmission.lean").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "DelegatedDifferential.lean"
        path.write_text(source + "\n" + "\n".join(assertions) + "\n", encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=ROOT, text=True, capture_output=True, timeout=300)
        if proc.returncode:
            print(proc.stdout[-16000:], file=sys.stderr)
            print(proc.stderr[-16000:], file=sys.stderr)
            raise SystemExit(proc.returncode)
    print(f"PASS: 72 real SQLite histories, {len(assertions)} kernel-checked projections; no universal runtime refinement claim")


if __name__ == "__main__":
    main()
