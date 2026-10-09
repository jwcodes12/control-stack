# SC-08: opt-in sealed-memfd script handoff (2026-10-09)

The frozen SC-08 reference launcher hashes a program fd, but gives the
interpreter a script by pathname in a same-UID-owned, 0700 pin directory.
A peer of that UID can chmod and mutate the 0400 pinned script between
verification and the interpreter's subsequent open. See the independent
negative witness in PR #16.

This change introduces an **opt-in**, Linux-only `--sealed-script` flag.
After reading and digest-checking the source script, the broker constructs a
memory-backed file containing *those bytes*, applies
`F_SEAL_WRITE | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_SEAL`, verifies the seals,
and keeps the fd alive across the Python interpreter's `execve`.
The interpreter reads `/proc/self/fd/N`, not a writable path. The broker
closes the fd after child completion. If memfd sealing is unavailable, it
fails closed instead of falling back to a writable script copy.

`tools/test_sc08_sealed_script.py` tests immutable bytes under a same-UID
write attempt, execution from the descriptor, and a post-hash source-path
replacement against the actual launcher. No preregistered evidence has been
changed or rerun; the default path and default config values are unchanged.
The new mode requires its own preregistered experiment before an assurance
claim is updated.

## Important boundaries

- This repairs only the **checked script bytes → Python script load** gap
  for the opt-in mode. It does not prove complete exec mediation, script
  semantic harmlessness, or integrity of the interpreter and OS.
- Same-UID ptrace or `/proc/pid/mem` access to the trusted broker is still a
  major concern. Running the broker under a distinct, inaccessible principal,
  with protected mounts and processes, remains necessary. A same-UID attacker
  must not be able to issue arbitrary broker RPCs or directly execute code.
- Kernel memfd seals and `/proc/self/fd` semantics are trusted environmental
  assumptions, not Lean theorems. The existing SC08 abstract model treats
  checked and executed script contents as identical by assumption.
- This opt-in mode emits an fd pathname; the path-only `reconcile_v2` checker
  has not been updated to treat sealed-fd provenance as a verified receipt.
  Never mark it equivalent to digest-named disk pins without an independent
  descriptor/provenance proof.

## Reproduce

```bash
python3 tools/test_sc08_sealed_script.py -v
python3 -m unittest scenarios/SC-08/harness/test_pin_isolation_boundary.py -v
```

The second command requires PR #16's test to be merged; the command is
listed as an independent reproduction step, not as proof this branch
contains that file.
