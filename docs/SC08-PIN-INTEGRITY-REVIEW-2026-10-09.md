# SC-08: pinned-script isolation boundary (2026-10-09)

**Status:** new reproducible negative permission-boundary witness. This is NOT a completed concrete-to-model refinement, an attack on the recorded run, or new deployment evidence. The SC-08 assurance status remains CONDITIONAL; frozen receipts and preregistration are unchanged.

## The issue

The launcher in scenarios/SC-08/harness/launcher.py hashes the interpreter through an open descriptor and invokes that descriptor, but gives the interpreter a checked script using a PATHNAME. The script is copied to a 0700 launcher directory with file mode 0400. POSIX permissions do not isolate processes that run as the SAME owning UID: such a peer can chmod the owned 0400 file to writable and replace the contents, including after the launcher verifies an existing pinned copy and before the interpreter opens the path.

The reference driver launches the broker and client under the same UID. The toy workload intentionally restricts the agent to the broker RPC, and the scripts are benign. Therefore this is a gap in any stronger claim about hostile same-UID clients, NOT an assertion that run-1 was compromised.

## Negative witness

Run: python3 -m unittest scenarios/SC-08/harness/test_pin_isolation_boundary.py -v

The test starts with a 0700 directory and 0400 checked script, runs a separate subprocess under the same UID, and demonstrates that the peer can change the bytes. A successful test demonstrates a missing isolation premise; it is not a failed recorded hypothesis and is not itself an exploit of the restricted RPC-only driver.

## Outstanding operational refinement obligations

1. Model check/open/read/hash, pending spawn, pinned script storage, UID/mount ownership, and the interpreter's *actual loaded bytes* as distinct concrete states and events.
2. Permit an adversarial filesystem mutation between the digest check and interpreter read in the general concrete machine. Only a separately stated effective isolation premise may exclude it.
3. Provide an abstraction map and per-event simulation to SC08.Op.exec; do not emit an abstract successful execution until the loaded-bytes/checked-digest relation is established.
4. Keep direct exec, execveat, memfd, JIT, interpreter/deputy paths, kernel mediation, digest collisions, trusted identities, and log/sentinel integrity as explicit unresolved assumptions.
5. Supply a check-disabled counterexample changing the successful bad-event outcome; build the result with Lean and standard axioms and obtain independent statement-fidelity review.

## Required runtime hardening

A different service UID or inaccessible mount for trusted pin storage, or a truly immutable and descriptor-addressed verified script object, may close this class of race. None has been implemented or tested by this document. Any change to the launcher must be separately preregistered and tested; do not rewrite frozen evidence to fit a stronger model. The residual implementation_conformance trust root remains open.
