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
no agent or alternate deputy having bypass authority, **if the IR faithfully
captures the runtime**. Faithfulness includes exhaustive scoped capabilities,
path alias/mount resolution, all processes using the specified launcher, actual
UID bindings, exact protocol transitions, byte/hash bindings, no database rollback,
clock and durable publication semantics. It is a substantial residual premise,
not a synonym for a passed test. Lean derives exclusive sink authority from explicit
finite IR facts; it does not postulate `CompleteMediation` as a separate axiom.

A result expires upon any changed mounts (including aliases), UIDs, role mappings,
credentials or inherited descriptors, image digests, network topology, runtime
inventory, launcher, receiver or broker hashes, approved policy, shared budget,
or storage/clock configuration. Recollect and reverify; no validity duration or
continuous drift monitor is claimed.

Supported input is a single pinned, normalized Compose **JSON** file (a YAML subset),
absolute long-form bind mounts (including a common `/channel` bind for the broker and its callers), numeric non-root users for every role, digest-pinned images and one internal
network, with a separate selected runtime-facts JSON inventory (UIDs, image digests,
mounts, networks and environment variable names only). The broker hosts `/channel/broker.sock` through its writable channel bind; agents, reviewer and approver see the same source through read-only channel binds. Connection submission is permitted, while the broker authorizes each operation separately. Missing shared channel inspection becomes UNKNOWN, not a guessed path from a role name. The inventory is caller
supplied: RUNTIME_OBSERVED labels do not authenticate it. Synthetic fixtures use
invented image digests and are not runnable container images. Live checks execute
the existing native confined broker/receiver on this box and test the corresponding
boundary; they do not claim the synthetic Compose deployment was launched.

Unsupported: arbitrary YAML/interpolation/overlays, builds or mutable image tags,
non-bind volumes, secrets, devices, host network/privileged containers, unknown
sidecars or dynamic deputies, root agents, user namespaces/UID remapping, symlink
or aliased protected sources without faithful resolution, external host helpers,
HTTP sinks, Kubernetes, WASI, non-Linux systems, arbitrary filesystem destinations,
whole-host containment, semantic approval quality and general network safety.
Unsupported features introduce UNKNOWN authority edges and an UNASSURED verdict.
UNKNOWN never means denied. Policy-forbidden but reachable paths remain bypasses.
