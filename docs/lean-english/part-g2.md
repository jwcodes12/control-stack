# Plain-English statements, part g2 (SC-08 to SC-14)

Conventions used throughout. All files are under `ControlStack/`. Every scenario model here is a small abstract transition system: a state, a list of operations ("a trace"), a `step` function, and a `Checks` record of switches (`full` = all switches on). "Any trace" means every list of operations of the model's `Op` type, including operations that carry any caller identity number the adversary likes. A caller identity in an operation is only a number the operation *claims*; nothing in these files checks that the claim is true unless the file says so (that is the `credential_separation` premise). A "recorded" run/use/decision/firing is an entry in a log inside the model state; whether the real system does only what the log records is a world assumption, not something Lean proves.

---

## SC-08: Unauthorized process or executable runs

**Harm.** A program runs whose loaded-content digest is not on the allowlist, or an interpreter runs a script whose digest is not on the script allowlist (or runs with no script at all).

**World assumptions (all NOT_PROVED):** credential_separation (trusted-role identities are the principals' own acts); complete_exec_mediation (every exec, including loaders, memfd and JIT, goes through the digest policy); fd_pinned_hash (the bytes hashed are the bytes loaded); honest_usefulness (the allowlist covers honest tasks).

**What the Lean claims, taken together, and what they leave to assumptions.** In a model where every exec is decided by a gate that looks up the digest (a function the model treats as given) of the file's current content and consults an allowlist (and, for interpreters, a script allowlist), the gate's record of runs contains only allowlisted programs and, for interpreters, only allowlisted scripts, for every sequence of file writes and exec requests, and nothing changes after an admin halt. This is a proof about the model's own run log. The gap is everything that connects that log to a real machine: that no exec path bypasses the gate, that the hashed bytes are the loaded bytes, that the digest function is collision-resistant (here it is an arbitrary function, with no property assumed), that interpreters are correctly listed as interpreters, and that the halt caller is really an admin.

### `ControlStack.SC08.sc08_safe`  — `ControlStack/Scenarios/SC08Exec.lean:171`
- **Says (plain English):** Start from any file system (any list of path/content pairs) with nothing yet run and not halted. After any sequence of writes, exec requests and halt requests, run with all four checks on (digest check, noexec mount check, script check, halt check), every entry in the model's list of runs is "ok": the program's digest is on the program allowlist, and if the program's digest is on the interpreter list, the run carried a script whose digest is on the script allowlist.
- **Under these hypotheses:** The configuration `Env` is arbitrary (digest function, writable paths, noexec mounts, program allowlist, interpreter list, script allowlist, path allowlist, admin list): no condition on it at all. The initial files and the trace are arbitrary. The only conditions are structural: initial state has an empty run list and is not halted; the checks are `full`. Model conditions only; the world assumptions (complete mediation, fd-pinned hashing, honest usefulness, credential separation) are not hypotheses of the theorem and are not proved.
- **Does NOT say:** (1) That a real process with a non-allowlisted binary cannot run: only that the model's gate never records one, so every real exec path must go through that gate (complete_exec_mediation). (2) That an interpreter is recognised as one unless the environment lists its digest in the interpreter list: an allowlisted interpreter missing from that list runs any script. (3) That allowlisted programs are harmless, or that honest tasks can run (an empty allowlist satisfies the statement).
- **Kind:** general theorem (induction over the trace; it is `safe_of_sound` at the `full` configuration).
- **Non-vacuity:** `ControlStack.SC08.honest_execs` (a decide-checked example with `E0`, `s0`: an allowlisted tool and an interpreter with an allowlisted script both run). Necessity of each check is shown separately by the `*_breaks` witnesses (not in this scenario's theorem list).
- **Read depth:** full

### `ControlStack.SC08.safe_of_sound`  — `ControlStack/Scenarios/SC08Exec.lean:164`
- **Says (plain English):** The same safety statement for any configuration of checks in which the digest check and the script check are turned on, whatever the other two checks (noexec mount, halt) are set to: after any trace from any initial files with no runs, every recorded run has an allowlisted program digest and, for interpreters, an allowlisted script digest.
- **Under these hypotheses:** `Sound C`: the digest switch is on and the script switch is on. Nothing else about the switches, the environment, the initial files or the trace. Model condition only.
- **Does NOT say:** (1) That the noexec or halt checks are unnecessary in the real system (it shows only that this one property does not need the noexec check; `sc08_safe` is its `full` instance and the file calls the noexec check "defence in depth"). (2) Anything about path-based allowlisting (the digest switch must be on). (3) Anything about the real digest function or the real loading path.
- **Kind:** general theorem.
- **Non-vacuity:** `sound_full` (the `full` configuration is sound), and `honest_execs` as above.
- **Read depth:** full

### `ControlStack.SC08.halt_freezes`  — `ControlStack/Scenarios/SC08Exec.lean:191`
- **Says (plain English):** If the model state is already halted, then in the `full` configuration any further sequence of operations leaves the entire state exactly unchanged: no file write takes effect, nothing more runs, and the halted flag stays set.
- **Under these hypotheses:** The state is halted; the configuration is `full` (in particular the halt check is on). The environment and the trace are arbitrary. Model conditions only.
- **Does NOT say:** (1) That a halt is ever issued or processed (the halt operation only works if the caller number is on the admin list; no liveness is claimed). (2) That programs already started before the halt stop running: the model has no notion of a running process, only of exec requests being recorded. (3) Anything about the world outside the model state.
- **Kind:** general theorem (the "frozen once halted" check is built into `step`, so the proof is a short induction: close to definitional).
- **Non-vacuity:** `no_halt_check_breaks` shows halting matters in the model (a decide example), and the hypothesis `halted = true` is reachable from `halt 9` with admin 9 in that example. No named theorem exhibits a halted state satisfying this exact statement beyond that.
- **Read depth:** full

---

## SC-09: Agent obtains privileged host access or passwordless sudo

**Harm.** A process of the agent's lineage holds or uses a capability that was not granted to its lineage and is not covered by an exact elevation rule.

**World assumptions (all NOT_PROVED):** credential_separation; kernel_enforces_caps (the OS enforces the capability model, no kernel bugs); admin_separation (agents do not hold admin grant authority); honest_usefulness (honest tasks need only granted capabilities).

**What the Lean claims, taken together, and what they leave to assumptions.** In the model, capabilities enter a lineage only through an operation that claims an admin identity, children get a subset of their parent's capabilities, executing a binary adds nothing, deputy calls need the caller to hold the capability, and elevation works only for an exact (binary, argument) rule. Under those switches (`full`), every capability held and every recorded privileged use traces back to an admin grant or an elevation rule, for any trace. The gap is that "admin" is just a caller number the operation claims (admin_separation and credential_separation), that the switches `attenuate`, `exactArgs`, `deputyCheck` are modelled platform behaviour, and that the log of "uses" is the model's record, not what the kernel actually permits (kernel_enforces_caps).

### `ControlStack.SC09.sc09_safe`  — `ControlStack/Scenarios/SC09Priv.lean:261`
- **Says (plain English):** Starting from the empty state (no processes, no grants, no recorded uses, not halted) and running any sequence of operations with the `full` checks, two things hold. First, every capability that any process holds belongs to a pair (lineage, capability) that appears in the grant table, which only grows when an operation claiming an admin identity issues a grant. Second, every recorded privileged use is either by a lineage that was granted that capability, or goes through an elevation rule in the trusted rule list whose binary and arguments match the recorded ones exactly and whose capability is the one used.
- **Under these hypotheses:** The policy `P` (admin list, elevation rule list, file-capability table) is completely arbitrary, including arbitrary elevation rules. The trace is arbitrary, with arbitrary caller numbers (so an operation may claim to be an admin; the theorem then treats it as a real admin act). The checks are `full`. Model condition only; kernel enforcement, admin separation and credential separation are not hypotheses.
- **Does NOT say:** (1) That the agent never obtains a capability: it holds whatever an op claiming an admin identity grants. (2) That any elevation rule is safe: an elevation rule applies to any live process of any lineage (the elevation clause does not check that the lineage was entitled to that rule), and rules are trusted by assumption. (3) That the real kernel cannot be bypassed, or that the list of recorded uses is all the privileged actions that really happen.
- **Kind:** general theorem (induction over the trace from `init`).
- **Non-vacuity:** `ControlStack.SC09.honest_privileged_work` (decide example with policy `P0`: a granted capability is used, an exact elevation rule fires, a child keeps a capability the parent passes on).
- **Read depth:** full

### `ControlStack.SC09.spawn_attenuates`  — `ControlStack/Scenarios/SC09Priv.lean:264`
- **Says (plain English):** In one spawn step in the `full` configuration, from a non-halted state where the parent process exists and the child number is unused, any process that appears in the new state but not in the old one (that is, the child) has the same lineage as the parent and a capability list that is a sub-collection of the parent's capability list at that moment.
- **Under these hypotheses:** The state is not halted; the parent `p` is found with record `q`; the child number `ch` is not already in use; the list of capabilities to keep (`keep`) is arbitrary. These are conditions on one state, not on traces.
- **Does NOT say:** (1) Anything about a multi-step trace; trace-level control of capabilities is `sc09_safe`. (2) That a child cannot later receive more capabilities (an admin `grant` can add them; the grant table is what bounds it). (3) Anything when the child number is already in use or the parent is missing (then no child is created).
- **Kind:** general theorem (one-step property; follows almost directly from the definition of spawn, which filters the parent's capabilities by `keep`).
- **Non-vacuity:** `honest_privileged_work` includes a spawn of process 2 from process 1 keeping capability 7 and using it.
- **Read depth:** full

### `ControlStack.SC09.halt_freezes`  — `ControlStack/Scenarios/SC09Priv.lean:286`
- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace leaves the whole state unchanged: no new process, grant or privileged use.
- **Under these hypotheses:** The state is halted; the checks are `full` (including the halt check); the policy and the trace are arbitrary. Model condition only.
- **Does NOT say:** (1) That a halt is ever triggered or processed (liveness). (2) That processes already running stop or lose capabilities in the real OS. (3) Anything about operations outside the model.
- **Kind:** general theorem (frozen-after-halt is built into `step`; short induction, close to definitional).
- **Non-vacuity:** `no_halt_check_breaks` (decide example showing a halt is reachable and matters).
- **Read depth:** full

---

## SC-10: Agent weakens host firewall or security policy

**Harm.** An enforcement decision uses a policy version that was not written by an admin, or was not the latest version at that moment.

**World assumptions (all NOT_PROVED):** credential_separation; store_trusted (the policy store's access control and storage are trusted, no rollback); single_evaluator (the store is the deployed evaluator's only policy source); honest_usefulness (admin policy changes are timely). The checks `singleEval` and `pinnedPath` are platform properties (environment premises), not gate behaviour.

**What the Lean claims, taken together, and what they leave to assumptions.** In the model, the store accepts a policy write only from an operation claiming an admin identity, every decision reads the latest version, and the alternative evaluator path and the search-path toolchain path are closed by switches. Then every recorded decision cites the latest stored version at that moment, and that version was written by a claimed admin. This is about which version a decision cites and who wrote it; the model never computes whether a request is allowed or what the firewall does, and the two attack paths (alternate evaluator, agent-writable path) are neutralised by environment flags set to "on" in `full`, not defeated by a mechanism proved in Lean. The gap is the world: that the real evaluator reads only this store, that the store cannot be rolled back or tampered with, and that identities are authentic.

### `ControlStack.SC10.sc10_safe`  — `ControlStack/Scenarios/SC10Policy.lean:212`
- **Says (plain English):** From the empty initial state, after any trace of the model's operations (policy writes by any caller, cache refreshes, decisions through either path, edits to the agent-writable policy file and search path, builds, halts), in the `full` configuration: (a) every recorded enforcement decision cites a stored policy version that was the latest one at that moment (its index plus one equals the store length recorded then), whose stored value equals the value the decision used, and whose writer is on the admin list; and (b) every recorded build used something whose digest equals the pinned digest.
- **Under these hypotheses:** The pinned toolchain location has the pinned digest (`hpin`: the environment's digest function applied to the pinned location equals the pinned digest). This is a world assumption written as a hypothesis ("the pinned location holds the pinned content"). The trace is arbitrary, with arbitrary caller numbers. The configuration is `full`, in which the stale-cache path is not used for decisions, the alternate evaluator `altDecide` is a no-op, and builds always use the pinned location rather than the agent-writable path.
- **Does NOT say:** (1) That the firewall or policy semantics are correct or that the decision allowed or blocked anything: a decision is only a record (request, version, value, store length) and no verdict is computed. (2) Part (b) is essentially the hypothesis restated: in `full` a build records the pinned location, so its digest is the pinned digest exactly by `hpin`; the theorem adds nothing about whether the real toolchain at that location is the pinned one. (3) That the real evaluator has no other policy source or that the store cannot be rolled back (single_evaluator, store_trusted).
- **Kind:** general theorem (induction over the trace), with part (b) definitional/trivial given `hpin`.
- **Non-vacuity:** `ControlStack.SC10.honest_enforcement_and_build` (decide example with `E0`: an admin policy is written, a decision uses version 0 with length 1, a build uses the pinned toolchain). `E0` satisfies `hpin`.
- **Read depth:** full

### `ControlStack.SC10.policy_admin_only`  — `ControlStack/Scenarios/SC10Policy.lean:217`
- **Says (plain English):** After any trace from the empty state in the `full` configuration, every stored policy version was written by a caller whose number is on the admin list.
- **Under these hypotheses:** Same as `sc10_safe`: the pinned location has the pinned digest (`hpin`), which is not used for this conclusion but is carried because the proof reuses the shared invariant. The trace and caller numbers are arbitrary; the configuration is `full` (admin-only writing is on).
- **Does NOT say:** (1) That the writer is a real admin: "admin" is the caller number claimed by the operation (credential_separation). (2) That the written policy is good (admins can write anything). (3) That the store holds the policy the evaluator actually uses.
- **Kind:** general theorem (induction over the trace; the `adminOnly` check is built into the step, so this is close to definitional).
- **Non-vacuity:** `honest_enforcement_and_build` (an admin write of policy 5 by admin 9 is recorded).
- **Read depth:** full

### `ControlStack.SC10.halt_freezes`  — `ControlStack/Scenarios/SC10Policy.lean:233`
- **Says (plain English):** If the state is already halted, then in the `full` configuration no further operation changes the state: no new policy version, decision or build.
- **Under these hypotheses:** The state is halted, the configuration is `full` (halt check on); the environment and trace are arbitrary.
- **Does NOT say:** (1) That a halt is ever issued or processed, or that the real firewall stops enforcing or freezes on halt. (2) That decisions or builds already in flight are stopped. (3) Anything about the real policy store beyond the model's state.
- **Kind:** general theorem (the freeze is built into `step`; short induction, close to definitional).
- **Non-vacuity:** `no_halt_check_breaks` (decide example with a halt reachable and a build blocked after it).
- **Read depth:** full

---

## SC-11: Agent tampers with container mounts, host filesystem or trusted toolchain

**Harm.** A build uses a toolchain whose digest differs from the pinned one, or mount/policy configuration is changed by a non-admin.

**World assumptions (all NOT_PROVED):** credential_separation; pinned_location_protected (the pinned toolchain location is not agent-writable); honest_usefulness (the pinned toolchain suffices for honest builds). The check `pinnedPath` is a platform property (environment premise).

**What the Lean claims, taken together, and what they leave to assumptions.** The two theorems are the SC-10 theorems; this scenario has no model of its own. They say that in the policy-store model, every build records the pinned location, so its digest equals the pinned digest (given a hypothesis that the pinned location holds the pinned content), and every stored policy version was written by a claimed admin. The model has no containers, mounts or host file system: "mount configuration" is not distinguished from any other policy value (a number), and the toolchain claim is closed mainly by the hypothesis that the pinned location holds the pinned digest and by the flag that routes builds to the pinned location. What is left to assumptions is the entire physical claim: that the pinned location is not writable by the agent, that nothing but this store configures mounts, and that identities are authentic.

### `ControlStack.SC10.sc10_safe`  — `ControlStack/Scenarios/SC10Policy.lean:212`
- **Says (plain English):** From the empty initial state, after any trace of policy writes, cache refreshes, decisions, edits to the agent-writable policy file and search path, builds and halts in the `full` configuration: every recorded decision cited the latest stored policy version at that moment and that version was admin-written; and every recorded build used something whose digest equals the pinned digest.
- **Under these hypotheses:** The pinned location has the pinned digest (`hpin`, a world assumption stated as a hypothesis); arbitrary trace and caller numbers; configuration `full` (admin-only writes, fresh decisions, single evaluator, pinned-path builds, halt check all on).
- **Does NOT say:** (1) That the build toolchain is the pinned one in reality: the build record is the pinned location itself, so the toolchain conclusion is `hpin` restated; the agent-writable search path (`writePath`) is ignored by `full` because the `pinnedPath` switch routes builds to the pinned location. (2) Anything about container mounts or the host file system: only the abstract policy log and build digests exist in the model. (3) Anything about a compromised compiler at the pinned digest (the scenario excludes it).
- **Kind:** general theorem; the build part is definitional/trivial given `hpin`.
- **Non-vacuity:** `honest_enforcement_and_build` (decide example with `E0`, which satisfies `hpin`).
- **Read depth:** full

### `ControlStack.SC10.policy_admin_only`  — `ControlStack/Scenarios/SC10Policy.lean:217`
- **Says (plain English):** After any trace from the empty state in the `full` configuration, every stored policy version was written by a caller on the admin list.
- **Under these hypotheses:** The pinned location has the pinned digest (carried, not used for this conclusion); arbitrary trace and caller numbers; configuration `full`.
- **Does NOT say:** (1) That a mount table or any host configuration is covered: the model stores opaque policy numbers with no meaning, and no mount-specific operation exists; the scenario's "mount/policy configuration changed by a non-admin" is covered only to the extent the real mount configuration is the store's content and only changes through it. (2) That the writer is really an admin (identity is a claimed number). (3) That an admin's change is correct.
- **Kind:** general theorem (the admin check is built into the step; close to definitional).
- **Non-vacuity:** `honest_enforcement_and_build`.
- **Read depth:** full

---

## SC-12: Agent establishes persistence, spawns helpers or recursively replicates

**Harm.** After its session ends or a HALT, an entity of the agent's lineage is still live, or a scheduled job of that lineage fires.

**World assumptions (all NOT_PROVED):** credential_separation (partly reduced in Lean: forged identity claims have no effect, the residual premise is that the platform's reported identity is the true issuer); registry_complete (every creation path goes through the trusted registry); revocation_effective (revoking a registry entry actually kills it); honest_usefulness (honest sessions can spawn the helpers they need). The check `registryOnly` is a platform property.

**What the Lean claims, taken together, and what they leave to assumptions.** In the model, every entity or scheduled job the agent creates is registered under its true lineage, ending a session or a halt revokes the whole lineage, and the unregistered creation path (`bypass`) is closed by a switch. Then no live entity belongs to an ended session, and no job of an ended session fires again, for any trace. The authenticated version adds that every live entity's session was started by an operation actually issued by an admin, and a concrete example shows what happens if a forged admin claim is accepted. The gap is that "no unregistered creation path" is an environment switch (registry_complete), that "revoked means dead" is the model's list removal (revocation_effective), and that the model has no runtime harness: live entities are model records.

### `ControlStack.SC12.sc12_safe`  — `ControlStack/Scenarios/SC12Persistence.lean:231`
- **Says (plain English):** From the empty state, after any trace of session starts, registered spawns, bypass attempts, firings, session ends and halts, in the `full` configuration: every live entity is registered, and the session it truly descends from (its ghost "origin") is currently active and has never ended. So nothing belonging to a session that has ended is live.
- **Under these hypotheses:** The admin list is arbitrary; the trace is arbitrary, including arbitrary claimed session labels for spawns and bypass attempts. The configuration is `full`: creation only through the registry (so `bypass` does nothing), the child's session label is taken from the parent (the child's claimed label is ignored), ending a session revokes its whole registered lineage, and the halt check is on. Model conditions; the world assumptions (registry_complete, revocation_effective) are not hypotheses.
- **Does NOT say:** (1) That nothing escapes in a real system: unregistered creation paths (cron, systemd timers, cloud jobs, credentials) are excluded only by the `registryOnly` switch, i.e. by assumption. (2) That anything the agent did while the session was live is undone (the scenario scope excludes it). (3) That revocation really kills the real process or job.
- **Kind:** general theorem (induction over the trace).
- **Non-vacuity:** `ControlStack.SC12.honest_session_lifecycle` (decide example: session 1 starts, spawns a job, the job fires once, the session ends, the job no longer fires and nothing is live).
- **Read depth:** full

### `ControlStack.SC12.no_fire_after_end`  — `ControlStack/Scenarios/SC12Persistence.lean:264`
- **Says (plain English):** Take any state satisfying the model's invariant in which session `sess` is already in the ended list. Then after any further trace in the `full` configuration, the log of job firings restricted to jobs whose true lineage is `sess` is exactly what it was before: no new firing of any job of that lineage ever occurs.
- **Under these hypotheses:** The state satisfies the invariant `Inv` (every live entity registered with its label equal to its origin and origin active; active and ended lists disjoint; every earlier firing recorded before its lineage ended). `Inv` holds from the empty state by the model's own lemmas but is stated here for an arbitrary invariant state. The session is in the ended list. The configuration is `full`; the trace is arbitrary.
- **Does NOT say:** (1) That firings before the end did not happen or were harmless (the log of earlier firings is unchanged, not empty). (2) That a real cron/timer/cloud job cannot fire: only registered jobs are modelled (registry_complete). (3) That a halt always lands: it covers sessions already in the ended list, which includes every active session after a halt.
- **Kind:** general theorem.
- **Non-vacuity:** `honest_session_lifecycle` (a state of this shape is reached in that example: session 1 ended, the post-end `fire 5` adds nothing).
- **Read depth:** full

### `ControlStack.SC12.halt_freezes`  — `ControlStack/Scenarios/SC12Persistence.lean:279`
- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace leaves the entire state unchanged: no new session, helper, job or firing.
- **Under these hypotheses:** State halted; configuration `full` (halt check on); admin list and trace arbitrary.
- **Does NOT say:** (1) That a halt is issued or processed (liveness). (2) That already-running real processes stop (the halt removes registered live entries from the model's list; revocation_effective is a premise). (3) Anything outside the model state.
- **Kind:** general theorem (every operation is a no-op once halted by construction; close to definitional).
- **Non-vacuity:** `no_halt_check_breaks` (decide example showing a halt is reachable and matters).
- **Read depth:** full

### `ControlStack.AuthInstances.sc12_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesB.lean:172`
- **Says (plain English):** Run the SC-12 model so that each operation carries a true issuer number and an operation that claims an identity (session start, session end, halt claim the caller; spawn, bypass and fire claim no identity) is applied only if the claimed identity equals the issuer; otherwise it is dropped. Then, for any trace of (issuer, operation) pairs: the same safety property as `sc12_safe` holds (every live entity registered, its origin session active and not ended), and for every live entity there is, in the trace, an operation issued by some admin `c` (not in `U`) of the form "start session with this entity's origin number" claiming `c`.
- **Under these hypotheses:** The admin list is arbitrary; `U` is any list of numbers none of which is on the admin list (this is the only hypothesis, a statement about how `U` was chosen); the trace is arbitrary. Model condition only. The real-world premise that the issuer number is the genuine platform-reported identity (and that the agent can only issue as members of `U`) is not in Lean; the theorem does not require that all agent operations carry issuers in `U`.
- **Does NOT say:** (1) That the issuer number is authentic: that is the residual premise (platform identity equals true issuer). (2) That spawns, bypass attempts and firings are authenticated (they claim no identity and are applied for any issuer). (3) The "not issued by `U`" conclusion is immediate from the admin-list membership and the hypothesis on `U`, so it carries no extra content beyond "an admin-claimed start operation, issued by that admin, exists in the trace".
- **Kind:** refinement/bridge (reduces the claimed-identity premise to an issuer-authenticity premise; first conjunct is `sc12_safe` transported through the authenticated run).
- **Non-vacuity:** NOT SHOWN for this exact statement (no named witness with a non-empty authenticated trace); `honest_session_lifecycle` shows the underlying SC-12 model is non-trivial, and `forged12_spawns_without_auth` below is a concrete trace.
- **Read depth:** full

### `ControlStack.AuthInstances.forged12_spawns_without_auth`  — `ControlStack/Scenarios/AuthInstancesB.lean:188`
- **Says (plain English):** A concrete example with admin list containing only 9, in which agent 1 issues two operations, "start session 5 claiming to be admin 9" and "spawn helper job 6 from entity 5". If no authentication is applied (no operation claims any identity), both are applied and two entities are live. If the SC-12 claims are authenticated, both operations do nothing (the start claim by issuer 1 for admin 9 is dropped, and the spawn then finds no entity 5) and nothing is live.
- **Under these hypotheses:** None beyond the concrete example (admin list [9], `full` configuration, the two-operation trace `forged12`).
- **Does NOT say:** (1) That authentication is sufficient (it is one concrete trace, not a general result). (2) That real identity authentication exists. (3) That other forgeries are caught.
- **Kind:** negative control (shows that without the authentication guard the forged admin claim succeeds), proved by `decide`.
- **Non-vacuity:** This is itself a computed example.
- **Read depth:** full

---

## SC-13: Trusted monitoring and audit dispatch

**Harm.** A workflow effect is dispatched without its trusted audit record, or an agent disables the audit path.

**World assumptions:** exclusive_dispatcher (only the trusted dispatcher can effect real workflow execution), marked THEOREM_VERIFIED by the scenario; credential_separation (the untrusted app cannot obtain broker or dispatcher authority), NOT_PROVED; effect_vs_record (external side effects are reconciled with the transactionally recorded dispatch), NOT_PROVED; honest_usefulness, NOT_PROVED.

**What the Lean claims, taken together, and what they leave to assumptions.** In a model with three lists (requests, audits, effects) where only a trusted `dispatch` transition appends to audits and effects (in one step, audit first, same id), every effect id has an audit entry with the same id, no id is effected twice, and the audit list only grows, for any interleaving including app and crash/restart operations. `app_cannot_effect` says operations other than `dispatch` leave the effect list unchanged; that is true by how the model's operations are defined, so it does not by itself show an app cannot dispatch or effect in a real database. The "exclusive dispatcher" that the scenario lists as verified is, in the Lean file, a deployment correspondence that the file explicitly says is not claimed. The gap is the whole bridge from this list model to PostgreSQL privileges, the real broker, and reconciliation of external side effects.

### `ControlStack.AuditDispatch.trace_safe`  — `ControlStack/AuditDispatch.lean:82`
- **Says (plain English):** Take any state in which every recorded effect id also appears in the audit list and the effect list has no duplicates. After any sequence of the model's operations (request, app event, app schema, dispatch, crash, restart), the final state again has: every effect id appears in the audit list, no effect id is repeated; and the old audit list is an initial segment of the new one (audits are append-only).
- **Under these hypotheses:** The starting state satisfies the invariant (every effect has an audit entry; effects have no duplicates). The model's dispatch step is enabled only for an id that was requested and not yet effected, and appends the audit then the effect for that id together. No condition on who issues which operation.
- **Does NOT say:** (1) That the audit was written before the effect in time: this theorem states only that the effect's id is in the audit list at the end (ordering within one step is a separate lemma, `dispatch_audit_first`, not part of this theorem). (2) That an agent cannot disable or alter the audit path in a real system (append-only is a property of the model's operations, not of real database privileges, which the file says are tested separately). (3) Anything about completion-time auditing or about real workflow execution happening only through the dispatcher.
- **Kind:** general theorem (induction over the trace).
- **Non-vacuity:** NOT SHOWN by a Lean example in this file; the empty state satisfies the invariant by inspection, and a `request` followed by `dispatch` of that id yields a non-empty effect list by unfolding `step`.
- **Read depth:** full

### `ControlStack.AuditDispatch.app_cannot_effect`  — `ControlStack/AuditDispatch.lean:91`
- **Says (plain English):** For any state and any operation that is not a dispatch, the effect list after the step is the same as before.
- **Under these hypotheses:** The operation is not a dispatch operation for any id (so it is one of request, app event, app schema, crash, restart).
- **Does NOT say:** (1) That the real application cannot cause a real effect: the model defines the app's capabilities as the non-dispatch operations, and the file states that real exclusivity depends on PostgreSQL privileges and the broker/worker credentials being the dispatcher's alone. (2) That the app cannot choose what gets dispatched: a `request id` from the app makes any id eligible for the dispatcher. (3) That `dispatch` is only called by the trusted party.
- **Kind:** definitional/trivial (proved by case analysis on the operation; the model's non-dispatch operations are defined not to touch the effect list).
- **Non-vacuity:** Hypothesis holds for any non-dispatch operation (e.g. `request 1`); no named witness.
- **Read depth:** full

---

## SC-14: Agent consumes runaway compute, tokens, network or budget

**Harm.** Cumulative metered usage of some resource exceeds its cap, a rate window is exceeded, or work runs after expiry.

**World assumptions:** credential_separation (NOT_PROVED); trusted_meter (the meter sees all consumption of every resource), NOT_PROVED; anti_rollback (the ledger is never rolled back), marked THEOREM_VERIFIED by the scenario, "reduced in Lean" under a trusted monotonic anchor; honest_usefulness (honest jobs fit their budgets), NOT_PROVED.

**What the Lean claims, taken together, and what they leave to assumptions.** In the SC-14 model, each work step carries a usage vector of three resources that the trusted meter reports; a step is admitted only if each resource's cumulative total stays under its own cap, the current time window stays under its rate limit and the clock is before the expiry. With the one excluded operation (storage rollback of the counters), the admitted usage always satisfies the caps, rate limits and expiry, and nothing is added after a halt. The anti-rollback theorem is a generic result about any gate with a specification: a trusted monotonic anchor makes released effects equal a plain, rollback-free run. But it is stated for arbitrary gates; the file lists the SC-28 instance (`sc28_rollback_safe`), and no theorem in the files read here instantiates it for the SC-14 model, so combining SC-14 safety with rollback is not itself a Lean statement. The gap is the meter (that "actual usage" in the model equals real consumption), the clock (a window is a span between model `tick` operations), the anchor, and record integrity.

### `ControlStack.SC14.sc14_safe`  — `ControlStack/Scenarios/SC14Runaway.lean:215`
- **Says (plain English):** Start from an empty ledger (nothing spent, clock 0, any chosen expiry) and run any trace of work steps, clock ticks, admin expiry changes and halts that does not contain a storage rollback. In the `full` configuration: the sum of the actual usage vectors of all admitted work is within the cap, resource by resource (compute, tokens, network); in every time window (the stretch between ticks) the sum of actual usage is within the per-window rate limit, resource by resource; and every admitted work step happened at a clock time before the expiry that was in force when it ran.
- **Under these hypotheses:** Caps, rates and admin list are arbitrary. The trace contains no rollback operation (the "legal" premise, which is the anti-rollback assumption). The "actual usage" attached to each work step is the metered value; the agent's own report is ignored. Refused work (one that would exceed a cap, rate or expiry) is not recorded and is treated by the model as consuming nothing. Expiry can be changed only by an operation claiming an admin identity. Model conditions only; trusted meter, trusted clock and credential separation are not hypotheses.
- **Does NOT say:** (1) That real consumption is within caps: the usage numbers are whatever the operation labels "actual"; a resource the meter does not see (or work refused by the gate but run anyway) is outside the model (trusted_meter). (2) A real-time rate bound: a window ends only when a `tick` operation occurs, and ticks are arbitrary trace operations; real-time rates need the clock premise. (3) That the expiry is the intended one: an operation claiming an admin identity can move it (credential separation).
- **Kind:** general theorem (inductive invariant over the trace).
- **Non-vacuity:** `ControlStack.SC14.honest_work` (decide example with `E0` caps (10,10,10) and rate (5,5,5): work in two windows is admitted and recorded). Necessity witnesses (`aggregate_cap_breaks`, `reported_cost_breaks`, `rate_burst_breaks`, `no_expiry_breaks`, `rollback_double_spends`) are in the same file.
- **Read depth:** full

### `ControlStack.SC14.halt_freezes`  — `ControlStack/Scenarios/SC14Runaway.lean:229`
- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace of operations (including a rollback) leaves the list of usage records unchanged: no work is admitted after a halt.
- **Under these hypotheses:** The state is halted; configuration `full`; the trace is arbitrary and need not be rollback-free. The conclusion concerns only the usage list (the spent counter may still be reset by a `rollback` operation).
- **Does NOT say:** (1) That the whole state is frozen (only the usage record list is; a rollback can still reset the spent counter, which does not matter for the usage list). (2) That a halt is ever issued or processed. (3) That real work already running stops.
- **Kind:** general theorem (once-halted checks are built into `step`; short induction, close to definitional).
- **Non-vacuity:** `no_halt_check_breaks` (decide example showing a halt is reachable and matters).
- **Read depth:** full

### `ControlStack.AntiRollback.rollback_transfer`  — `ControlStack/Core/AntiRollback.lean:205`
- **Says (plain English):** For any gate `G` (a state, an operation type and an effect log) with a specification `S` (an inductive invariant and an acceptability predicate for effects), and any initial state satisfying the invariant, consider the machine that stores each new state as a versioned record in a store, keeps every record ever written as a backup, and has a trusted monotonic anchor holding the last committed record. After any interleaving of writes, commits, restarts and rollbacks of the store to any previously written backup, with the anchor checks on: the anchored state equals the plain run of the gate over the committed operations; the effects released to the world equal exactly the effects of that plain run; the specification's invariant holds of that state; every released effect is acceptable in that state; and the anchor version equals the number of committed operations.
- **Under these hypotheses:** `G` and `S` are arbitrary (any gate with a spec), the initial state satisfies the invariant, and the trace is arbitrary. Model conditions: the anchor is monotonic and not resettable by the operator, a write is accepted only when the store equals the anchor (otherwise the machine halts), a commit or restart-recovery advances the anchor only when the store is exactly the next record after the anchor, and the operator can only restore records that were actually written (record integrity: it cannot forge records). The anchor and record-integrity premises are world assumptions the Lean model builds in as the machine's behaviour.
- **Does NOT say:** (1) That the anchor exists in a real system or is tamper-proof: its trust is the residual premise. (2) That the SC-14 model is covered: the theorem is for any gate, but the SC-14 ledger is not instantiated here (the SC-28 budget model is, in `sc28_rollback_safe`); for SC-14 one would also need its spec, whose own acceptability predicate (`ok`) only records the expiry condition (the caps and rates live in its invariant). (3) That real consumption occurs only after commit: effects are "released" at commit, so work done in the real world before the anchor advances is outside the model; also no liveness (a rolled-back machine fails closed and halts).
- **Kind:** general theorem (inductive invariant `RInv`).
- **Non-vacuity:** `nonce_replay_without_anchor`, `rollback_without_anchor_double_spends` (decide examples where rollback is accepted and the anchored machine refuses the replay and halts), `honest_liveness` (without rollbacks every op commits), and `sc28_rollback_safe` (a concrete instantiation).
- **Read depth:** full
