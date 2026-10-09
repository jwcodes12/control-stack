# SC-08 reconciliation v2: supplementary negative controls

This additional checker strengthens **log reconciliation**, not the kernel safety
theorem. It does not modify the frozen `PREREG-SC08-EXEC-v1` record or claim
new preregistered evidence.

The run-1 reconciliation only required an equal number of successful launcher
executions and sentinel receipts, and only checked digest membership **if**
the launcher happened to include its digest keys. That allowed a missing
launcher SHA-256 or an equal-count mismatch between different allowlisted
script digests to evade that check.

`reconcile_v2.py` fails closed for missing/malformed program/script hashes,
an unpinned executed script path, malformed/duplicate sequence IDs,
nonzero exits, and a discrepancy between the **multiset** of successful
launcher script digests and the independently recorded sentinel self-hashes.

`python3 -m unittest tools.test_sc08_reconcile_v2` exercises ten synthetic
receipt cases, including missing digest fields, same-count mismatches and a same-name path outside the configured pin root the v1 comparator would miss.

**Residual premises:** both logger and sentinel can lie, the process may not
hash exactly the bytes that were executed, the launcher can be bypassed, a
system-call-level race could occur, and trusted allowlists can be wrong.
The comparison gives no independent proof of any such runtime property.
A credible SC-08 refinement must still link fexecve's already-hashed fd and
the digest-named pinned script to `SC08.execResult`/the actual loaded bytes.
A new preregistration and run are needed before promoting this checker as
evidence.

The checker requires a trusted absolute `--pin-dir` argument and compares the resolved executed path with that digest-named file. This is an evidence-level path check, **not** a proof of pin-directory ownership, immutability or syscall integrity; those remain assumptions.
