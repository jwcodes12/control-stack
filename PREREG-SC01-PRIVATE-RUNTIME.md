# SC-01 private-runtime replication

Prospective protocol: replace host runtime-file binds with two independently
copied minimal Python runtime trees. Copy file bytes, never hard-link or reflink;
mount only the selected role's tree read-only. Prepare both before drawing any
secrets. Agent code is separately snapshotted per invocation. Keep the existing
namespaces, capability drop, ledger, task contract and deadline unchanged.

This is a targeted file-cache mitigation, not VM isolation or a secrecy proof.
CPU caches, scheduling, clocks, shared kernel resources and host integrity remain
unresolved. No KVM device or installed VM runner is available on this host.

Before measurement, inventory all copied regular-file hashes and device/inode
identities; reject any cross-role alias, source alias or content mismatch. Run
secret-free namespace preflights in both roots. Require real probe execution.

Cache experiment: repeat the existing fixed four warm/cold controls and 64
independent uniform 32-bit-secret trials on the legacy shared-runtime harness as
a positive control. Then run the identical encoder/decoder for 64 fresh-secret
trials with separate roots and constant NULL gateway views. Do not require the
old decoder's warm/cold controls to succeed in the private-root condition: their
failure is the predicted effect. Report both exact-rational two-sided 95%
Clopper–Pearson intervals (tail 1/40), every trial and faults, and whether the
private-root one-sided 95% lower bound exceeds 1/2. No significance or absence of
detected leakage establishes zero capacity or bounds adaptive attacks.

Usefulness: repeat the existing paired 64-lifetime, five-episode task using the
private roots for both conditions. Keep its preregistered simultaneous intervals
and 90% completion floor. Separate measurements from historical runs; no pooling.

Evidence binds new sources, existing scenario sources, runtime inventory and
platform identity. Preserve failures, reject missing isolation, stale source
bindings and promotion to runtime secrecy certification. Review meaningful
results with Opus xhigh and Astra high before deciding the next milestone.
