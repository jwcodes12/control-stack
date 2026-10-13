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
semantics. A concrete replay of the archived Tier 2 clean transcript is kernel-checked in
`deployment/TIER4-TRANSCRIPT.md` (the first three attempts, which failed on a tactic parsing
error, are kept in `deployment/TIER4-TRANSCRIPT-BLOCKED.md`). It is one archived run, with
the log's completeness as a premise.

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
  against `r2-v0`); a socket-side HALT is retried (idempotent) up to four times, about 60 s, and 4 of the 12 connection slots are reserved for reviewer/approver/admin UIDs so agents and strangers cannot starve it; the
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
- **Sink scope is `<release_id>.body` names.** A receiver crash before `link` leaves a
  `.pending-*` temporary file (possibly a prefix of reviewed bytes). **Fixed from source
  generation `r2-v3` (T9.5):** each delivery reaps, under the DB writer lock, every
  regular, singly-linked, receiver-owned `.pending-<32 hex>` file before publishing (a
  two-link file is the post-link state and is still reconciled, not reaped; anything else is
  left alone). The debris of a crash is thus removed by the next delivery, not at crash time;
  the sink-side audit still reports any non-`.body` file, and none occurred in recorded runs.
- **Limits found by the review of the T9 fixes** (`deployment/reviews/t9-hardening-review-opus.md`,
  a model review of the author's own fixes; no independent human has seen them). Status after
  Tier 10 (below): evidence from `r2-v0` still ran a broker whose delegation could not be turned
  off, so for it the sink audit (canonical `<id>.body` names, bytes equal to the release digest,
  zero delegation rows) remains the only evidence; the pin vault (and the template vault) is part of the TCB. The other
  limits found by that review are addressed in Tier 10, as stated below, and a model review of those changes
  (`deployment/reviews/t10-open-items-review-opus.md`) found no HIGH issue and one MEDIUM, fixed.

## Tier 10: closing the open engineering items

Source generation `r2-v7` (`r2-v6` was the first Tier 10 generation; the review's L1 fix changed `server.py`, so the live evidence was redone on `r2-v7` and the `r2-v6` runs are kept under `deployment/runs/tier10/gen-r2-v6/`). Each item has a regression test; none has had independent human review.

- **`Principals` refuses UID 0** (review L5). UID 0 ignores every file permission the role
  boundaries use, so it can no longer be a role. The root-run broker tests now run the broker and
  the admin calls as a disposable non-root admin UID.
- **The receiver refuses delegated releases by default** (`deliver_record(..., allow_delegation=False)`,
  `deliver_cli --allow-delegation`). A database that holds a delegation grant or a delegated-executor
  row is no longer delivered unless the trusted caller asks; the broker already refused to start on one.
- **Evidence checkers bind one source generation and refuse `python -O`.** `pins.require_generation`
  requires every recorded source digest to belong to the current tree or to one vaulted generation
  (a mixture no deployment ran is rejected; a complete record must equal the generation's whole file
  set); `pins.generation_holding` does the same for partial records (the boundary-evidence checker, and the
  two claim pins of a replayed collection). Hardened-profile archives must come from the current tree or from
  `r2-v3` or later (the first generation with delegation off, the threaded broker and the reaper). Replay of an
  archive whose host observations predate the `/slice` inventory still skips that rule: the rule set is chosen
  by which keys were recorded, not by the generation. Every `check_deployment_*` script and the `deployment` package refuse to run under `-O`,
  where `assert` disappears. The hardened remediation templates embed the source pins, so their
  digests are vaulted too (`deployment/pinned-templates/`, `pins.py vault-templates`).
- **The image scan inventories the whole `/slice` tree** and the interpreter start-up hooks
  (`*.pth` and any `sitecustomize`/`usercustomize` module in any form, anywhere in the image). `/slice` is first on `sys.path`, so a stray
  `.pyc`, an extra module that shadows the standard library, a symlink, a group/other-writable file
  or a file owned by a role UID makes the image UNKNOWN
  (`image-slice-tree-differs-from-reference-UNKNOWN`). The first live attempt of the new check caught
  documentation files that the image builder had shipped into the import tree
  (`deployment/runs/tier10/gen-r2-v6/attempt1-NOTE.txt`); the builder now adds only the reference files, root-owned.
  The rest of the base image (the Python installation outside `/slice`) is still trusted, not inspected.
- **HALT availability.** An admin's HALT request sets an in-process latch: from that moment the broker
  starts no other mutating request, even while the database is too busy to record the HALT, and a HALT
  the caller gave up on, for any failure, is retried in the background for as long as that broker process lives (a restart starts
  with a fresh latch; the database's own `halted` flag is what survives). Staging has a total byte quota
  (64 MiB) so a stuck agent cannot make the database itself grow without bound. It does not stop an agent filling the host disk through its container's writable layer (the profile
  does not make the root filesystem read-only), so a separate filesystem for the database is a premise. Not fixed: a separate
  receiver process still depends on SQLite's own lock scheduling, and one agent can exhaust the shared
  staging quota for the other (availability, not safety). (Tier 11 below mitigates both.)
- **`cstack plan` accepts a fresh scan's own IR.** A scan's IR carries UNKNOWN reasons that replay rules
  do not produce; the planner now reproduces the IR under replay rules or under fresh-scan rules and
  requires one of them to match exactly.
- **Two simultaneous broker starts** hold an exclusive `flock` on `<socket>.lock` for the broker's life
  before probing the old socket, so neither can unlink the other's live socket.
- **`publish_effect` / `--effect-root` stay outside the claim.** The scanner treats the flag as an
  unknown launch argument (UNKNOWN); a test pins that, so the second file-effect path cannot appear in
  a CONDITIONAL deployment. Putting it under the claim would need its own model, scanner and review.
- **HTTP delivery is an outbox relay outside the claim (2026-10-13).** `tools/http_relay.py` is not in the pinned slice. It reads
  the broker database read-only, requires the whole release log to verify, and POSTs only sink files that have a publication
  receipt to a literal-loopback destination with an `Idempotency-Key`. It is at-least-once on the wire and exactly-once only at a
  destination that honours the key. Evidence: `deployment/runs/tier11/http-relay/`. HTTP sinks remain an unsupported feature of
  the scanner (UNKNOWN authority edges).
- **Kubernetes: static extractor only (2026-10-13).** `extractors/kubernetes/` maps a restricted Pod + default-deny NetworkPolicy
  manifest onto the Compose profile and inherits its UNKNOWN-edge rule for anything outside it. No cluster was run and there is no
  runtime collector, so a Kubernetes deployment is still outside the claim; the extractor is a step toward it, tested by a
  differential against the Compose reference and single-fault mutants (`tools/test_kubernetes_extractor.py`).
- **Transcript replay uses the recorded clock** instead of `now = 0`: the database's own
  `releases.created` for the two releases, with every expiry after it; a mutant with a later clock is
  rejected. That the recorded value is the broker's clock remains a premise.
- **Live evidence on the final generation** (`deployment/runs/tier10/`, final generation; the earlier `r2-v6` runs are in `gen-r2-v6/`): the five non-bypass hardened
  cases and the demo run on `r2-v6` and pass the independent checkers. Bypass cases were not rerun
  (defensive scope).
- **Held-out round 2** (`deployment/heldout/tier10`): 34 cases sealed by a separate blind `codex exec`
  author for the hardened profile before any scoring: 8 supported, 17 refuted, 9 unknown. Before any
  fix, the instantiated static evaluation produced **one false CONDITIONAL out of 26 negatives**
  (`agent-role-impersonation`: an agent whose `SLICE_ROLE` is `broker`; the fresh scan already marked
  this UNKNOWN, but the extractor, which does not read environment values, accepted it). That is the
  held-out figure. The extractor now checks `SLICE_ROLE`/`PYTHONPATH` under fresh rules and the
  re-scored result (0 false acceptances, 0 of 8 supported rejected, 22 of 34 UNKNOWN) is **contaminated**
  by that fix. The hand-written baseline caught 0 of the 26 negatives. The author is the same model
  family as the original builder and a different one from the fixer; it is not an independent human.

## Tier 11: persisted release log, per-agent staging quota, receiver lock retry (source generation `r2-v8`)

Changed trusted code: `trusted_stack/controller.py` and `trusted_stack/outbox_receiver.py` (generation vaulted by the pins recipe; hardened fixtures, templates
and goldens regenerated). Tests: `trusted_stack/test_release_log.py` (12) and `tools/test_deployment_r2.py` (new evidence tests). Live evidence:
`deployment/runs/tier11/` (README there lists the commands; two failed attempts caused by a missing `PATH` are kept). None of this has had independent human review.

- **Release log (the owner chose the "event log" option of `docs/lean-english/RELEASE-LOG-DESIGN.md`).** `release()` writes one `release_log` row in the SAME
  transaction as the approval consumption, the budget charge and the `releases` row: nonce, digest, destination, agent, lease, **signer** and **reviewer** as they were at
  that instant, and cost. `approvals.used`, `reviews` (which is `INSERT OR REPLACE`) and leases keep changing; the log row does not. SQL triggers refuse `UPDATE` and
  `DELETE` on it. The owner of the database can drop the triggers, so this is defence in depth, not custody. A logged release means the broker COMMITTED the release,
  not that the receiver received or published anything. The fields are the fields of the Lean `ReleaseEvent`
  (`ControlStack/Deployment/ReleaseLog.lean`); `test_runtime_columns_correspond_to_the_lean_release_event_fields` fails if they drift apart.
- **Publication receipt with an observed hash.** `deliver_record` reads the published file back, computes its SHA-256, requires it to equal the logged digest and
  stores it once in the append-only `publication_receipts`. The hash is computed by the receiver itself (trusted), so it is a record, not an attestation.
- **Per-agent staging quota.** Each agent's share is `STAGING_QUOTA // number of agents` (32 MiB with two agents); the shares never sum to more than the total, so one
  agent can no longer use up bytes another is entitled to. The total quota still applies; already-staged bytes stay free. Availability only. Tested at unit level, not under live load.
- **Receiver lock retry.** `deliver_record` retries a busy SQLite writer lock with jittered exponential backoff up to `LOCK_DEADLINE` (120 s) and then fails closed.
  It is a mitigation, not FIFO scheduling: the lock stays with SQLite, and starvation past the deadline is possible.
- **Older databases** are upgraded in place (idempotent `CREATE ... IF NOT EXISTS`) in the first staging or release transaction.
- **Independent check.** `deployment/reconcile.release_log_problems` (used by `check_container_run.py` and `check_remediated.py` for generation `r2-v8` and later) reads the
  SQLite backups and the sink: the log equals the `releases` list, costs sum to `spent`, nonces are unique, each row equals the approval it consumed, signer/agent/reviewer hold
  the pinned roles, each publication receipt names a logged release, carries its digest and destination and equals the SHA-256 of the sink file. Archives of earlier
  generations have no log and are skipped, not counted as checked.
- **Live evidence (this host, one run):** `containers-hardened`: five safe cases PASS with the log consistent in every phase; `crash-retry` shows the real killed-process state
  (one `release_log` row, sink file present, no publication receipt: admitted, delivered, not yet receipted) and the later recovery; `halt-inflight` likewise.
  `demo-dev-clone`: `cstack demo` PASS. No bypass case was launched.
- **What this does not do:** it is the same SQLite file as the state it describes, so there is no anti-rollback or custody for the whole file; log rotation is not designed; the
  `effect_release`/`publish_effect` path and `--effect-root` are as before (outside the claim); the Lean model of the log is model-only and its premises (durable log, atomic
  receipt, faithful extraction) are tested here on one host, not proved. `deployment_broker_safe` is unchanged.

## Post-Tier-10 Lean simplification (model-only; not a new release claim)

The next-phase proof work is staged in draft PR #55. The existing theorem
`Deployment.deployment_broker_safe` remains intentionally narrow: it establishes
that each nonce listed as published at the sink has a **used** approval in the final
abstract broker state, conditional on accepted IR, faithful authority extraction,
and `BrokerProtocolRefinement`. It does **not** conclude that published file bytes
or destination exactly match a past reviewed and signed release.

`Deployment.Provenance.deployment_broker_provenance` separately proves a
reachable-state **model invariant**: each retained final-state approval is
attributed to an approver-role signer, agent-role owner, staged digest, a current
reviewer-role record and a lease whose owner matches. A positive model trace and
an unreviewed-state counterexample are supplied in
`ControlStack/Deployment/ProvenanceWitnesses.lean`. This does not preserve
an immutable release-time reviewer/digest/destination/bytes receipt; review
entries can be overwritten, and the broker's release history stores a nonce but
no signed per-release content record. Exactly-reviewed bytes remain a guard on
the model transition and an implementation/refinement **premise**, not a
standalone theorem about the real receiver.

Named views now expose every conjunct of `TrustedBroker.Allowed`,
`Deployment.BaseAccepted`, and `Deployment.WritersChecked`, with bidirectional
equivalence to the original predicates; `Deployment.Accepted` already had
six named fields. These views are a proof-maintenance convenience, **not**
new stronger authorization checks. A reusable finite forward-simulation lemma
is instantiated by SC-25; it transports model claims and does not supply
OS/runtime correspondence.

**T4.2 disposition:** full `Accepted` monotonicity under edge deletion is
false, demonstrated by the three retained kernel countermodels. Only
`accepted_path_safety_monotone` (an accepted *larger* IR implies a no-bypass
property of an edge-restricted smaller IR with the same nodes/roles) is a
proved model claim. Do not say that the smaller IR is accepted.

These additional proofs are still model-authored, have had **no independent human
review**, and must pass the exact Lean 4.34.0 build, axiom review and static
checkers before being treated as kernel-checked in the updated branch. Scoped
R2 remains **CONDITIONAL**; G1 independent human review remains open.
