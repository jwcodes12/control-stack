# Trusted-path code review (Claude Opus 5.5, model review — not independent human review)

Date: 2026-10-11. Repository: `/var/tmp/sol-deployment-slice-20261010`, branch `sol/r2-tier8`, HEAD `f94eb38`.
This is a read-only review. No repository file was modified. I ran no containers and no network commands.
Gate: R2 "Security review: threat model and code review for the trusted path".

Reviewed against `docs/DEPLOYMENT-CLAIM-v0.md` (as of HEAD; it now lists delegation as unsupported, line 102) and `docs/DEPLOYMENT-QUICKSTART.md`.

Severity scale (from the request):
- **HIGH**: violates the stated claim.
- **MEDIUM**: the claim holds only under an unstated assumption.
- **LOW**: hardening or availability.

## Summary

| # | Sev | Area | Finding | Tests cover it? |
|---|---|---|---|---|
| — | — | Core effect path | **No HIGH found.** Approval binding, one-use nonce, lease and shared budget, SQLite isolation, staged-byte immutability, receiver publication, fsync ordering, receipts and HALT linearization match the claim. | Mostly yes |
| M1 | MEDIUM | Caller binding / claim | The broker always exposes `delegate`, so an approval can be consumed by an agent other than the one it is bound to. The claim calls delegation "unsupported" and says unsupported features yield UNASSURED, but nothing detects runtime delegation. The Lean `Allowed` predicate requires `a.agent = r.uid`. | Unit tests exercise delegation; nothing tests that it is off in the R2 deployment |
| M2 | MEDIUM | Framing / approver inputs | A slow sender can hold the single-threaded server indefinitely. Queued requests from clients that already timed out **commit later** (confirmed for HALT). An approver that retries with a fresh nonce after a timeout ends up with two approvals. | No |
| M3 | MEDIUM | Caller binding | SO_PEERCRED binding assumes agents cannot change UID. The Compose profile does not set `no-new-privileges` or `cap_drop`. Docker's default bounding set keeps CAP_SETUID, and the scanner checks setuid/setgid mode bits but not file capabilities. | No |
| L1 | LOW (priority) | Framing | **Pre-authentication broker crash:** any UID that can connect can send deeply nested JSON. The resulting `RecursionError` is not caught, so the serve loop exits and the socket is unlinked. The container entry always bootstraps, so the broker then cannot restart. Confirmed by a PoC. | No |
| L2 | LOW | HALT | `halt()` gives up after the 15 s SQLite busy timeout if a publication holds the writer lock longer, and reports Denied. | No |
| L3 `.pending-*` debris | **Fixed in `r2-v3` (T9.5):** `_reap_unlinked_pending` under the DB lock (unit test with a real SIGKILL before `link`; non-trusted names, symlinks, two-link files and HALT are left alone). Sink audit still reports any non-`.body` file. |
| L4 | LOW | Controller | `state()` does not convert `sqlite3.Error`, and the server does not catch it, so a long read lock would crash the broker. UNCONFIRMED: I found no agent-reachable trigger. | No |
| L5 | LOW | Principals | UID 0 is accepted for every role, and broker UIDs ≥ 2^31 never match (signed `3i` unpack; fails closed). | No |
| L6 | LOW | Startup | `server.py` bootstraps the DB before refusing an agent euid, and does not require the broker euid to be an admin. | No |
| L7 | LOW | Evidence | `deployment/reconcile.py` only checks the release→file direction. The claim's direction (file→release) is covered only by the separate full-directory listings in the harness/checkers. | Indirectly |
| L8 | Note | Tests | The `concurrent-cap1` container case is serialized by the single-threaded server, so it does not exercise SQLite contention. The unit test `test_concurrent_replay_exactly_once` does. | — |

---

## Areas that look sound (verified by reading)

**Approval binding (`controller.py:291-347`).** Inside one `BEGIN IMMEDIATE` transaction, `release` re-reads the approval by nonce and checks the following:
- digest, destination and lease equal the request;
- `used == 0`;
- the approval has not expired (`approval[5] <= now` denies);
- the signer is still an approver;
- the caller is the owner, unless the owner delegated (see M1);
- the lease belongs to the owner, is not revoked and has not expired;
- per-lease `used + cost ≤ budget` and global `spent + cost ≤ cap`, both read in the same transaction (`meta` is read after BEGIN IMMEDIATE in `_tx`, lines 165-169);
- the artifact re-hashes to the digest, and a review exists.

It then charges both budgets, sets `used=1`, and inserts `releases` (`nonce UNIQUE`) and, optionally, `effect_records`. All of this is one commit.

**Nonce reuse.** `approvals.nonce` and `releases.nonce` are primary key / UNIQUE, and `used` is checked. Re-approving a used nonce fails with IntegrityError, which `_tx` turns into Denied. Covered by `test_nonce_must_not_be_reissued` and `test_concurrent_replay_exactly_once`.

**Cost and integer values.** The server fixes `cost=1` (`server.py:60-63`), so "every release costs one unit" holds at the RPC boundary. `cost` cannot be supplied by agents (the payload shape check at `server.py:38` rejects extra keys). Budget, expiry and UID fields use `type(x) is int`, which rejects bools, floats and NaN. Oversized ints raise OverflowError at SQLite bind time, which `_tx` turns into Denied. A JSON integer with more than 4300 digits raises ValueError, which is caught. Negative or zero budget, cap and cost are rejected.

**Transactions.** Every connection uses `isolation_level=None` with explicit `BEGIN IMMEDIATE`, so writers are serialized across the broker and receiver processes. `synchronous=FULL` with the default rollback journal. Any exception path rolls back, or closes the connection, which also rolls back. `_open` refuses a DB whose parent directory is group/other-writable, which also prevents an attacker from planting a hot `-journal`.

**Staging to publication (no TOCTOU).** Artifacts are insert-once (`INSERT OR IGNORE`, with an explicit check that the stored bytes are the same). `effect_records.body` is copied from the artifact in the release transaction. The receiver re-hashes that body and checks the digest against the effect record, the release and the approval.

**Expiry and clock.** Comparisons are consistent (`<=` means expired) in the controller and the receiver. The receiver uses one clock sample for both expiries (`outbox_receiver.py:182`; there is a test for this). Clock rollback is the stated "trusted clock" premise, and the Lean model also allows arbitrary times.

**Receiver.**
- The file name is `str(int)+".body"` with `release_id` in the range 1..2^63-1, so path traversal is impossible. `destination` is never used as a path.
- The sink directory is opened with `O_DIRECTORY|O_NOFOLLOW`. The receiver requires that directory to be owned by its euid with mode `& 0o077 == 0`. POSIX ACL entries widen the group mask bits, so they are also rejected.
- Publication follows a strict order: temp file created `O_EXCL|O_NOFOLLOW` 0600 → write loop → `fsync(file)` → `link()` (does not overwrite) → `fsync(dir)` → unlink temp → `fsync(dir)` → receipt INSERT and commit. Publication is therefore durable before the receipt, as the claim states.
- A pre-existing name with different bytes, metadata or link count, or a symlink, fails closed. The only recovery allowed is the exact-inode `.pending-*` hardlink.
- Double delivery is prevented by the receipt row plus the file check. Concurrent receivers serialize on the DB lock.
- `deliver_record` is not reachable over the socket and requires euid ∈ admins.

**HALT.** `halt()` takes `BEGIN IMMEDIATE`. `_tx` and `deliver_record` check `halted` under the writer lock. There is no un-halt. An in-flight publication completes before HALT commits; after HALT, delivery of admitted-but-unpublished releases is refused. This matches the claim text (lines 34-37) exactly. Covered by `test_halt_delivery_races.py`, `test_outbox_receiver.py` and `test_joint_trace_oracle.py`. HALT *liveness* is not claimed (see M2, L1, L2).

**Caller identity in the deployed profile.** Each role has a distinct numeric UID; the broker and receiver both run as admin 23700. Agents mount only `/channel` read-only, owned by 23700 with mode 0755, so they cannot replace or plant the socket. `/private` and the sink are not mounted in agent containers. `docker exec` runs as the service user. I found no descriptor-passing path from a trusted client to an agent: `client.request` opens a fresh socket per call inside the trusted container.

**Approver inputs.** Only the approvers set may approve. A review by a distinct reviewer is required. The lease must be active and bound to the named agent.

---

## Findings

### M1 (MEDIUM): the deployed broker exposes delegation, which the claim calls unsupported and the model does not contain

**Where**
- `trusted_stack/server.py:31-32, 56-59` (ops `delegate`, `revoke_delegation`).
- `trusted_stack/controller.py:238-266` (`delegate`) and `314-321` (release accepts caller = delegate).
- Lean: `ControlStack/TrustedBroker.lean:97` (`Allowed` requires `a.agent = r.uid`).
- Claim: `docs/DEPLOYMENT-CLAIM-v0.md:9, 102-103, 108`.

**Scenario**
1. The approver issues nonce `n` bound to agent A (23701) and lease A.
2. A, attacker-controlled, sends `{"op":"delegate","nonce":"n","delegate_uid":23702}`.
3. B (23702) sends `effect_release` for `n`. The broker admits it, because the caller is the delegate and not the agent the approval is bound to.
4. The receiver publishes `<id>.body`.

The sink file is still attributable to a reviewed, approved, once-consumed, in-budget release. The `releases.agent_uid` column records the owner A, and `delegated_releases` records B as executor. So the attribution conclusion survives.

However:
- (a) The claim's "approval bound to … agent" and the ProtocolRefinement's "actual caller binding" do not hold literally for that release.
- (b) The claim says unsupported features "introduce UNKNOWN authority edges and an UNASSURED verdict". Delegation, though, is a runtime operation the agent can invoke under a CONDITIONAL verdict, and the configuration scanner cannot see it.
- (c) The Lean `Step` has no delegate transition. A delegated release refines to a model `release` only under a non-identity mapping that relabels the caller as the owner.

**Impact.** The claim holds only if one assumes either that no agent invokes `delegate`, or that the caller relabelling is acceptable. Neither assumption is stated.

**Fix.** Either drop `delegate`/`revoke_delegation` from `shapes` in the R2 broker (or gate them behind a flag that the scanner records), or change the claim to say: "approval bound to the owning agent; one-hop delegation lets one other agent UID execute it; refinement maps the executor to the owner".

**Tests.** `test_delegation.py` and `test_delegated_fleet.py` show that delegation *works* through `run_one`. No test asserts that it is disabled in the R2 deployment.

### M2 (MEDIUM): the slow-sender hold blocks the single-threaded server, and timed-out requests commit later

**Where**
- `trusted_stack/server.py:87-93`: the 5 s timeout applies to each `recv`, not to the whole frame, and the frame may be up to 1.5 MB.
- `server.py:82`: one connection is handled at a time, with `listen(16)`.
- `client.py:11`: 6 s client timeout.

**Scenario (confirmed by a PoC run as a local Unix socket in the scratchpad: a local proof-of-concept (not committed: defensive scope))**
1. Any UID that can connect sends one space byte every 3 s and never sends a newline. The server stays inside that connection, potentially for weeks (1.5 MB at about 3 s per byte).
2. Every other client, including admin HALT, times out after 6 s. PoC output: `halt via socket failed after 6.0s: TimeoutError`.
3. The timed-out requests are already in the kernel backlog with their bytes buffered. When the slow sender stops, the server processes them and **commits** them, even though the client was told it failed. PoC output: `halted in DB 10s after attacker stops (client was told timeout): True`.

**Safety relevance**
- **Approvals.** An approver whose `approve` times out and who then retries with a *new* nonce gets two committed approvals. That allows two sink files for one intended approval. Both stay within budget, and each is "exactly approved" on paper. The trusted approver input is thus manipulated through induced timeouts.
- **HALT.** HALT over the socket can be postponed indefinitely. During that time the receiver, which does not use the socket, keeps delivering admitted-but-unpublished releases. The claim does not promise HALT latency. The out-of-band path (calling `Controller.halt` as 23700 directly on the DB) still works and should be documented as *the* HALT path.

**Unstated assumptions.**
- Approver/admin clients treat a timeout as indeterminate, and retry only with the same nonce (a duplicate nonce is safely rejected).
- HALT is issued out of band.

**Fix.**
- Use a total per-connection deadline and a small frame cap for non-stage operations.
- Make requests idempotent or explicitly indeterminate on the client side.
- Optionally use a threaded server with per-UID connection limits.
- Document approver retry semantics.

**Tests.** None; `serve()` framing has no tests.

### M3 (MEDIUM): SO_PEERCRED caller binding assumes agents cannot gain CAP_SETUID

**Where**
- `server.py:84-85` trusts the kernel UID.
- `deployment/run_containers.py:110` allows only the service keys `x-cstack-role, user, image, environment, networks, volumes`. There is no `security_opt: no-new-privileges` and no `cap_drop: [ALL]`.
- `deployment/scan.py:56,107` flags setuid/setgid *mode bits* only.

**Scenario.** Agent containers run with Docker's default capability bounding set, which includes CAP_SETUID and CAP_SETGID, and without `no-new-privileges`. Suppose the image contained any binary that grants capabilities: a setuid-root file, or a file with `security.capability` xattrs, which mode bits do not show. An agent process could exec it, `setuid(23704)`, and connect. SO_PEERCRED would then report the approver, and the agent could approve its own staged content, or act as reviewer or admin.

**Current image.** On the source rootfs `/var/tmp/sc01-vm-assets/build-root` (Alpine, busybox) I found 0 setuid/setgid files and `getcap -r` reported no file capabilities. `/root` was unreadable to me, and I did not inspect the imported image itself, so this is UNCONFIRMED for the exact image ID. The fresh scanner would also catch mode-bit setuid.

**Impact.** The claim's attacker model says the attacker cannot change role assignment, and kernel bugs are in the TCB. The specific premise, though, is unstated: "agent containers cannot acquire CAP_SETUID (no setuid or file-capability binaries; no-new-privileges unset)". In the claim's terms, this is an edge the Compose scan does not model.

**Fix.** Require `security_opt: ["no-new-privileges:true"]` and `cap_drop: ["ALL"]` for agent services, and model their absence as UNKNOWN. Also inventory `security.capability` xattrs from the export, via `tarfile` `pax_headers` (`SCHILY.xattr.security.capability`).

**Tests.** None.

### L1 (LOW, fix before release): pre-authentication broker crash via deeply nested JSON

**Where**
- `trusted_stack/server.py:97`: `json.loads(data)` runs before any role check.
- `server.py:99`: the except tuple omits `RecursionError`, which is a `RuntimeError`, and omits `sqlite3.Error`.
- `server.py:109`: the `finally` unlinks the socket.
- `tools/deployment_container_entry.py:13`: the entry always passes `--bootstrap-cap`.
- `server.py:129`: `Controller.bootstrap` opens with `O_CREAT|O_EXCL`, so a restart raises `FileExistsError`.

**Scenario (confirmed by PoC a local proof-of-concept (not committed: defensive scope), using a caller UID in no role).**
1. Send `"["*200000 + "]"*200000 + "\n"`, which is 400 kB and under `MAX_REQUEST`.
2. Result: `server thread alive: False exception: ['RecursionError'] socket file exists: False`.
3. In the container the broker is PID 1 (via `execv`), so the container exits. `docker start` re-runs bootstrap against the existing DB and dies.

**Impact.** Everything fails closed (no new releases), and the receiver can still deliver already-admitted releases. However:
- the socket HALT path is gone;
- the outage persists until an operator intervenes;
- the socket is mode 0666 in a 0755 directory, so any local UID that can reach `/channel`, not only agents, can trigger it.

**Fix.**
- Catch `Exception` per connection, falling back to Denied.
- Bound the nesting depth, or reject frames that do not start with `{`.
- Bootstrap only when the DB is absent, never on every start.

**Tests.** None.

### L2 (LOW): HALT can fail on the busy timeout

**Where.** `controller.py:119-120` (`timeout=15`) and `349-361`.

If a receiver publication holds `BEGIN IMMEDIATE` for more than 15 s (slow fsync of a 1 MiB body on degraded storage, or a hung trusted process), HALT raises `Denied("halt persistence unavailable")` and nothing is persisted. The claim's wording ("HALT takes the same SQLite writer lock… a publication already holding it can finish before HALT commits") implies HALT waits, but HALT can in fact fail. Agents cannot hold the lock (their transactions are short), so this is not attacker-driven.

**Fix.** Retry HALT until it commits, or document that HALT is retried.

**Tests.** None (the race tests keep the hold under 15 s).

### L3 (LOW): pre-link crash debris in the sink

**Where.** `outbox_receiver.py:78-91`.

**Scenario.** The receiver crashes (SIGKILL or power loss) after creating `.pending-<hex>` and before `os.link`. The temp file, possibly holding a truncated prefix of the reviewed bytes, stays in the sink directory. Retrying the same release publishes through a new temp file, and the debris is never removed, because `_recover_interrupted_link_cleanup` only removes the inode that matches the published name.

**Impact.** The claim's "only supported effect is publication of exact reviewed bytes as `<release_id>.body`" holds for `*.body` names only. A sink consumer, or the harness `sink_snapshot`, which lists every file, would see an extra non-`.body` file. The trigger is a trusted-process crash, not an agent.

**Fix.** Scope the sink to `*.body`, or reap unmatched `.pending-*` debris under the DB lock. Also add a sentence to the claim.

**Tests.** `test_partial_hardlink_cleanup_crash_reconciles_exact_inode` covers the post-link case. The pre-link case is not tested.

### L4 (LOW, UNCONFIRMED reachability): `state()` error handling

**Where.** `controller.py:363-373`.

The queries in `state()` are not wrapped. A `sqlite3.OperationalError`, for example a read blocked past the busy timeout during an EXCLUSIVE commit, would escape `server.py:99` and crash the broker in the same way as L1. In rollback-journal mode, readers are blocked only during brief EXCLUSIVE commits, and I found no agent-controllable way to extend those.

### L5 (LOW): UID edge cases

- `Principals` accepts UID 0 (`controller.py:35`, `x >= 0`), and `server.py:122` uses bare `int()`. The claim's "nonzero UIDs" property is enforced only by the configuration verifier, not by the runtime.
- `struct.unpack("3i")` (`server.py:84-85`) reads the UID as signed. UIDs ≥ 2^31 become negative and match no role, so this fails closed. `deliver_cli._uids` bounds UIDs to 2^32-1, but the server does not.

### L6 (LOW): startup order

`server.py:128-133` runs `Controller.bootstrap` (creating the DB and parent checks under the current euid) *before* refusing an agent euid. It also never requires `geteuid() ∈ admins`, although the receiver requires the DB owner to be an admin. The setup is operator-controlled, so this is not attacker-reachable.

### L7 (LOW, evidence tooling rather than the trusted path): direction of reconciliation

`deployment/reconcile.py:15-20` iterates over `releases` and looks for each file. It never lists the sink, so an unattributed file (for example `2.body` in the writable-sink negative, where `admitted=0`) is not reported as inconsistent. The claim's conclusion runs file→release. That direction is currently established only by the full directory listings in `run_containers.sink_snapshot`, `deployment/check_remediated.py:49-51` and `tools/check_deployment_container_evidence.py:52-53`. Adding an "unattributed files" count to `reconcile.py` would make the sink-side check self-contained.

### L8 (Note): what the container race case tests

`run_containers.py:143-151` races two agents, but `serve()` handles one connection at a time, so the two `effect_release` transactions never contend in SQLite. The case demonstrates admission order, not SQLite locking. SQLite-level exclusivity is covered by the threaded unit tests (`test_controller.py:100`, `test_delegation.py:113`, `test_effect_service.py:79`, `test_multi_actor_receiver.py`).

---

## Checks performed

- Read in full: `controller.py`, `outbox_receiver.py`, `server.py`, `client.py`, `deliver_cli.py`, `tools/deployment_container_entry.py`, `deployment/run_containers.py`, `examples/compose-two-agent/clean.compose.json`, `deployment/reconcile.py`, the image-observer part of `deployment/scan.py`, `ControlStack/TrustedBroker.lean:1-160` and `ControlStack/Deployment/R2Contracts.lean:80-150`.
- `python3 -B -m pytest -q -p no:cacheprovider trusted_stack`: 58 passed, 2 skipped, 127 subtests passed.
- Two local proofs of concept (not committed), each running `server.serve` in a thread on a relative-path Unix socket inside the scratchpad, as the unprivileged user:
  - deep JSON crashes the broker (L1);
  - a slow sender starves HALT, and the timed-out HALT commits later (M2).
- Read-only listing of setuid/setgid files and file capabilities in the image source rootfs (M3).

## Not reviewed

- `trusted_stack/agent_confinement.py` (Landlock/seccomp launcher; the claim says it is not an enforcement premise of the container result), and `audit.py`.
- The scanner, collector, IR validator, verifier and Lean serializer, beyond the setid check in `scan.py`. The Lean proofs themselves, beyond reading `Allowed`, `Step` and `BrokerProtocolRefinement`.
- The actual imported Docker image (only its source rootfs), the Docker daemon, the kernel, SELinux labels, and the runtime behaviour of bind mounts.
- SQLite or Python internals; filesystem-specific durability (I assumed POSIX fsync semantics for the ext4/xfs-class directory fsync).
- The `tools/cstack.py` demo pipeline, `deployment/run_remediated.py` and `check_remediated.py`, beyond the sink-listing lines cited.
- Confidentiality (for example the permissions of the SQLite journal or the readability of artifact bodies); it is not part of the claim.

---

## Disposition (Tier 8, Claude)

Trusted code (`trusted_stack/`) was **not** changed in Tier 8. Every archived container run and the
offline image pin bind the current trusted-source hashes, and the archive replays compare against
the current sources. A trusted-code fix therefore first needs versioned historical pins (T9.1).

| Finding | Disposition |
|---|---|
| M1 delegation | Claim amended: covered runs must show zero delegation rows; new `deployment/sink_audit.py` checks this in the demo and over all 30+ archived runs (all zero). Disable in the R2 broker: T9.2. |
| M2 slow sender / late commit | Claim amended (retry only with the same nonce; direct `Controller.halt` stays the dependable HALT path). **Fixed in `r2-v2` (T9.3):** total frame deadline, bounded threads, per-UID connection cap; database-busy indeterminacy remains stated. Tests: `tools/test_deployment_hardening.py` (`Serving`). |
| M3 CAP_SETUID | Checked on the actual imported image: no setid files, no `security.capability` xattrs, agent-UID container CapPrm/CapEff/CapAmb = 0 (`deployment/runs/tier8/capability-check`). Premise stated in the claim. **Enforced (T9.4):** hardened profile requires `no-new-privileges` + `cap_drop: [ALL]` for agents (extractor UNKNOWN edge, v2 daemon inventory, fresh scan refuses v1); the image scan records `security.capability` PAX xattrs. Live evidence: T9.6. |
| L1 nested-JSON crash | **Fixed in `r2-v2` (T9.3):** every per-connection exception is DENIED, frames must begin with `{`, restart reopens the database and clears a dead socket. Regression: nested JSON then a normal request, and kill/restart. |
| L2 HALT busy timeout | **Fixed in `r2-v2` for the socket path:** `halt_with_retry` (4 attempts; other denials final). `Controller.halt` itself unchanged. |
| L3 `.pending-*` debris | Claim scoped to `<id>.body`; sink audit reports any non-`.body` file (none recorded). Reaper: T9.5. |
| L4, L5, L6 | L4 covered by the catch-all. L5: peer UID unpacked unsigned (`iII`); **UID 0 is still accepted by `Principals`** (the configuration verifier requires nonzero; the root-run broker tests would need reworking), so this part stays open. L6: fixed (agent/non-admin euid refused before any database is created). |
| L7 reconcile direction | Covered by `deployment/sink_audit.py` (file → release), with the archived writable-sink `2.body` as its negative control. |
| L8 | Noted in the review packet; SQLite contention is covered by threaded unit tests only. |
