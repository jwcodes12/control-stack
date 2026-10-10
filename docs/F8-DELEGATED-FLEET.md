# F8 delegated fleet: scope and verification

reviews/family-strengthening/DelegatedFleet.lean is a review-scoped,
kernel-checkable, non-vacuous model of **two independently approved releases
sharing one admission budget**, one of which may be delegated to a
distinct agent. It explicitly models grant, revocation, release by actual
caller, fixed-unit shared charging, publication and HALT in one state.

Theorems establish a global budget invariant for *arbitrary action lists*;
rejection of revoked delegated admissions and reclaimed owner tokens;
no publishing before admission; and no new publication transition once
halted. Two positive finite witnesses exercise both agents when cap=2 and
budget competition when cap=1.

This proof is about the stated transition system. It does NOT prove that
Python, SQLite, SO_PEERCRED, POSIX filesystem, Unix scheduling, host
permissions, or subprocess confinement implement it exactly.

trusted_stack/test_delegated_fleet.py independently checks the running
SQLite+local-filesystem service under concurrent agent and delegate
requests, one shared cap, restart, wrong actors, release then revoke
then dispatch, fault between publication/receipt followed by HALT,
and durable provenance tampering. Real broker UID tests and the
Linux process Landlock/seccomp profile are separate test surfaces.

Run:

    lake env lean reviews/family-strengthening/DelegatedFleet.lean
    python3 -m unittest trusted_stack.test_delegated_fleet -v
    python3 tools/delegated_lean_difftest.py

The existing 72-schedule differential remains finite and evaluates one
approval in the simulated Controller runtime. This additional model and
fleet regression do not establish an unbounded semantic simulation.
Full delegated system assurance additionally needs a proof of the actual
runtime's transition relation, trusted host identity/capability custody,
complete mediation, clock and persistence trust, crash semantics, and
review of the real OS/network adapters by an independent party. These
are not automatically discharged by valid Lean statements.
