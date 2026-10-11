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

Fresh schema 0.1 scans normalize YAML/interpolation through the recorded Compose
CLI and observe source realpaths and offline reference-image facts. YAML requires
explicit x-cstack.roles. See deployment/TIER3-SCANNER.md. Legacy v0 snapshots do not
gain these observations through schema-only migration.

Unsupported: lease or approval delegation (see the trusted-path review note below),
arbitrary overlays, builds or mutable image tags,
non-bind volumes, secrets, devices, host network/privileged containers, unknown
sidecars or dynamic deputies, root agents, user namespaces/UID remapping, symlink
or aliased protected sources without faithful resolution, external host helpers,
HTTP sinks, Kubernetes, WASI, non-Linux systems, arbitrary filesystem destinations,
whole-host containment, semantic approval quality and general network safety.
Unsupported features introduce UNKNOWN authority edges and an UNASSURED verdict.
UNKNOWN never means denied. Policy-forbidden but reachable paths remain bypasses.


The Tier 4 TrustedBroker theorem is `deployment_broker_safe`. It transfers graph
exclusivity, shared quota and one-use approval history to nonce-indexed sink effects
under `BrokerProtocolRefinement`: actual model transactions, caller bindings and
reverse-admission-order publication sublist. This is a substantive unproved link;
it permits admitted-but-unpublished records. It does not replace the older SC26
full byte-publication equality with a claim that image inspection verifies protocol
semantics. Concrete Tier 2 transcript replay did not pass its three-attempt limit;
see deployment/TIER4-TRANSCRIPT-BLOCKED.md. The model witness package is independent
of that blocked runtime replay, and remaining R2 tiers are still pending.

## Trusted-path review dispositions (Tier 8)

A model code review of the broker/receiver path (`deployment/reviews/trusted-path-code-review-opus.md`;
not an independent human review) found no violation of the conclusion above and three
premises that were previously unstated. They are now part of this claim:

- **Delegation is enabled in the deployed broker and invisible to the scanner.** An agent
  can call `delegate` so that the other agent UID executes its approval. Every sink file
  stays attributable to a reviewed, exactly approved, once-consumed, in-budget release,
  but "bound to agent" and "actual caller binding" then hold only under a refinement that
  maps the executor to the owning agent. The Lean `Allowed` rule has no delegate step.
  This claim therefore covers only runs whose sink-side audit
  (`deployment/sink_audit.py`) records zero `delegations` and `delegated_releases`
  rows; every archived and demo run satisfies this. **Fixed from source generation `r2-v1`
  (T9.2):** the broker command line rejects `delegate` and `revoke_delegation` unless
  `--allow-delegation` is given, refuses to start on a database that already holds
  delegation rows, and the scanner marks an entry that passes the flag UNKNOWN
  (`broker-delegation-enabled-outside-claim-UNKNOWN`). Evidence archived under generation
  `r2-v0` (every Tier 2-8 live run) still relies on the sink audit; live evidence on `r2-v1`
  is queued (T9.6).
- **Client timeouts are indeterminate, and HALT has no latency bound.** Approvers must retry a
  timed-out approval only with the **same nonce** (duplicates are rejected), never with a
  fresh one, because a request can still commit after its client gave up whenever the
  database is busy (the controller waits up to 15 s; the client waits 6 s). HALT has no
  latency bound; the dependable HALT path remains a direct `Controller.halt` call as the
  admin UID. None of these produce an unapproved sink file. **Fixed from source generation
  `r2-v2` (T9.3):** the broker handles each connection on a bounded thread with one total
  3 s read deadline for the whole frame, at most 2 connections per caller UID and 12 in
  all, so a slow sender can no longer stall other callers or make queued requests commit
  later; a frame must begin with `{`; every per-connection failure, including a deeply
  nested request, is answered DENIED instead of ending the service (the crash recorded
  against `r2-v0`); a socket-side HALT is retried until it commits (it is idempotent); the
  broker refuses to start unless its UID is an admin and not an agent, before touching the
  database; a restart reopens the existing database (the cap must agree) and clears only a
  dead socket it owns. Archived `r2-v0` runs predate these fixes; live evidence on the new
  generation is queued (T9.6).
- **Agent UIDs cannot gain CAP_SETUID.** SO_PEERCRED binding assumes agents cannot switch
  UID. Evidence for the pinned offline image (`deployment/runs/tier8/capability-check`):
  no setuid/setgid files, no `security.capability` xattrs, and an agent-UID container has
  empty permitted/effective/ambient sets (CAP_SETUID only in the bounding set). Regaining it
  would require a kernel-level escalation, which is in the TCB. **Enforced from the
  hardened profile (T9.4):** `examples/compose-two-agent-hardened/` gives both agents
  `security_opt: [no-new-privileges:true]` and `cap_drop: [ALL]`; the collector reports both
  from the Docker daemon (v2 inventory: `hardening`); the extractor makes an agent that lacks
  either, or whose daemon report disagrees with the declaration, an UNKNOWN edge
  (`agent-no-new-privileges-and-cap-drop-ALL-not-established`); any other `security_opt` or
  `cap_drop` value stays an unsupported feature; a fresh scan refuses an inventory that does
  not report `hardening`; and the image scan records files carrying `security.capability`
  (from the `SCHILY.xattr` PAX header of `docker export`), which make the image UNKNOWN. The
  reading is unit-tested on a synthetic archive and has a positive control on a real image
  that carries one file capability (`deployment/runs/tier9/capability-xattr-probe`).
  Archived runs (v1 inventories, before this profile) replay under the rules they were
  produced with and do not satisfy the hardened profile; remediation plans now add both settings
  to the agents. Live evidence under the hardened profile is queued (T9.6).
- **Sink scope is `<release_id>.body` names.** A receiver crash before `link` can leave a
  `.pending-*` temporary file (possibly a prefix of reviewed bytes) that is not cleaned
  up. The sink-side audit reports any non-`.body` file; none occurred in recorded runs.
