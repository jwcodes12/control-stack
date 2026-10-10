# Local file deployment claim v0

This is one conditional assurance case for the existing Linux local-file receiver,
not a general Compose or whole-host security certificate. The protected sink is
one private directory owned by the broker/receiver UID. Its only supported effect
is publication of exact reviewed bytes as `<release_id>.body`; an approved
`destination` is metadata, never a pathname. There are exactly two untrusted agent
UIDs, separate reviewer and approver identities, one trusted broker/receiver owner,
exact one-use approval bound to digest, destination, agent, lease and nonce, and
one shared positive budget. Every release costs one unit in the runtime.

The attacker controls either or both agent programs and requests, may substitute
payloads, replay nonces, race agents, request forbidden roles, and attempt direct
writes or alternate deputies. The attacker cannot change the pinned snapshot,
trusted code, role assignment, private database, sink directory, Linux kernel or
trusted approval inputs. Semantic correctness or harmlessness of approved content
is outside this claim.

The TCB is enumerated: Linux kernel and filesystem permission/UID implementation;
Landlock and libseccomp with the launcher `trusted_stack/agent_confinement.py`;
Python interpreter and libraries; Unix socket `SO_PEERCRED` server and framing;
`trusted_stack/controller.py`, SQLite transaction/locking/durability, private DB
and its containing directory; `trusted_stack/outbox_receiver.py` and trusted
receiver process; trusted reviewer, approver and admin operators; SHA-256 and its
exact-byte use; trusted clock; host/container operator and mount/credential
custody; the read-only JSON collector, IR validator, verifier and Lean-instance
serializer; and Lean kernel with pinned libraries. None is independently audited
by this slice. Configuration extraction does not prove kernel enforcement.

The broker commit point is the SQLite transaction committing approval consumption,
release record and shared budget charge. The protected effect point is durable
publication by atomic non-overwriting link and directory fsync. The receipt commits
later, so publication and receipt are not a cross-resource atomic transaction.
HALT takes the same SQLite writer lock: a publication already holding it can finish
before HALT commits; HALT stops new publication after its commit and cannot retract
past bytes. A crash after publication can leave a file without a receipt. Do not
model this receiver with the generic sticky-bit gate's instantaneous cancellation.

The conditional conclusion is that every scoped sink file is attributable to a
reviewed, exactly approved, once-consumed release within the shared budget, with
no agent or alternate deputy having bypass authority, subject to two distinct,
unproved residual premises:

1. **Faithful extraction**: the finite IR exhausts actual effective authority,
   including path aliases, mounts, processes, UID bindings, descriptors and pinned
   source/image correspondence.
2. **Protocol refinement**: the implementation executes the model's transitions
   with authentic role bindings, exact approval/byte hashes, unit costs, trusted
   clock, no rollback and matching durable publication. In particular,
   `ProtocolRefinement.publication : sinkEffects = model.bank` assumes the **full
   model–runtime correspondence of sink effects**, not merely faithful IR capture.

Passing tests or hashing sources proves neither premise universally. Lean derives
exclusive direct sink authority from finite facts without a CompleteMediation
axiom. **Lean and Python check the same finite configuration obligations:**
transitive reachability excluding broker/receiver, every agent/trusted UID and
trusted role separation, exact role counts, runtime match, exact sink/database
writers, nonzero UIDs, and absence of unknown or isolation escape authority.
The raw projection is evaluated and each result proved by the Lean kernel.
`deployment/runs/tier1/differential.json` records all 26 fixtures and 250
seeded random mutations with zero differences. The additive test records 520
mutations with zero negative-to-positive changes; this is a finite regression
experiment, not a universal theorem over arbitrary repairs. A skipped Lean check
always yields UNASSURED; CONDITIONAL requires both checks.

The actual theorem uses separate `ExtractionFaithful` and `ProtocolRefinement`
structures. `ExtractionFaithful` carries effective-authority inclusion and receiver
identity correspondence. `ProtocolRefinement` carries gate identity, actual caller
binding, unit costs, and the full sink/model publication equation. Neither structure
is automatically proved by a daemon snapshot or a successful concrete run.

A result expires upon any changed mounts (including aliases), UIDs, role mappings,
credentials or inherited descriptors, image digests, network topology, runtime
inventory, launcher, receiver or broker hashes, approved policy, shared budget,
or storage/clock configuration. Recollect and reverify; no validity duration or
continuous drift monitor is claimed.

Supported input is a single pinned, normalized Compose **JSON** file (a YAML subset),
absolute long-form bind mounts (including a common `/channel` bind for the broker and its callers), numeric non-root users for every role, digest-pinned images and one internal
network, with a separate selected runtime-facts JSON inventory (UIDs, image digests,
mounts, networks and environment variable names only). The broker hosts `/channel/broker.sock` through its writable channel bind; agents, reviewer and approver see the same source through read-only channel binds. Connection submission is permitted, while the broker authorizes each operation separately. Missing shared channel inspection becomes UNKNOWN, not a guessed path from a role name. The selected inventory is unauthenticated. Synthetic inventories remain static
negative controls; live inventories are captured from `docker inspect`, retain a
hash of raw daemon output, and explicitly disclaim independent attestation. The
local offline imported image is pinned by its content-addressed Docker image ID,
with trusted code baked in and a build/source manifest. The runnable clean Compose
fixture is the artifact scanned and exercised in the real-container experiment.

That experiment covers mounts and numeric UIDs under Docker's default seccomp,
namespaces and UID mapping. Landlock is inactive on this host and is **not** an
enforcement premise of the container result. The earlier native Linux guest checks
separately include Landlock/libseccomp. A writable-sink negative also relaxes sink
DAC to 0777; a writable bind alone does not defeat directory mode 0700. The UID
collision negative demonstrates agent authority to HALT as admin, observed as an
empty sink and a denied subsequent honest task; it does not demonstrate a direct
sink write without a sink mount.

Unsupported: arbitrary YAML/interpolation/overlays, builds or mutable image tags,
non-bind volumes, secrets, devices, host network/privileged containers, unknown
sidecars or dynamic deputies, root agents, user namespaces/UID remapping, symlink
or aliased protected sources without faithful resolution, external host helpers,
HTTP sinks, Kubernetes, WASI, non-Linux systems, arbitrary filesystem destinations,
whole-host containment, semantic approval quality and general network safety.
Unsupported features introduce UNKNOWN authority edges and an UNASSURED verdict.
UNKNOWN never means denied. Policy-forbidden but reachable paths remain bypasses.
