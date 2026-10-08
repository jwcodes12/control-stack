# Circle handoff — 2026-10-08 (branch `claude/circle`, worktree /var/tmp/cs-circle, based on master eb0200e)

Read first: `reviews/circle-consult-2026-10-08/synthesis.md`, `PRIMITIVES-AND-SCENARIOS.md`, `NECESSITY.md`.

Done:
- Consultations (Astra xhigh, Fable). Prompts, reviews, metadata and synthesis are under
  `reviews/circle-consult-2026-10-08/`.
- `ControlStack/Leakage.lean` (15 theorems) and `ControlStack/Necessity.lean` (4 witnesses). Standard axioms only;
  the full `lake build ControlStack` passes (3717 jobs).
- `tools/check_sc01_case.py` reworked (exit 3 on a refuted hypothesis); multi-axis assumptions in
  `assurance/sc01-safety-case.json`.
- `tools/ctrlcert.py` and `tools/test_ctrlcert.py`.

Separate branch (main checkout): `sc01-vm-host-check-20261008`.
- `cda2b10`: link-race fix.
- `9d4d785`: the frozen usefulness gate FAILED on the QEMU pair because every agent exceeds the 0.25 s deadline
  under TCG.
- Owner decision needed: a deadline amendment or hardware isolation.

Not merged and not pushed. To merge: `git -C ~/research/control-stack merge claude/circle`. It touches ROADMAP.md,
assurance/sc01-safety-case.json and tools/check_sc01_case.py. The new files would not conflict.

Verification:
- `lake build ControlStack`
- `python3 tools/check_sc01_case.py` (expected exit 3, HYPOTHESIS_REFUTED)
- `python3 tools/test_ctrlcert.py`

Next steps: see PRIMITIVES-AND-SCENARIOS.md §3.
