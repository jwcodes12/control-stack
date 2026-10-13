# English statements under test

### Claim 1
## `ControlStack.SC08.sc08_safe`

- **Says (plain English):** Start from any file system (any list of path/content pairs) with nothing yet run and not halted. After any sequence of writes, exec requests and halt requests, run with all four checks on (digest check, noexec mount check, script check, halt check), every entry in the model's list of runs is "ok": the program's digest is on the program allowlist, and if the program's digest is on the interpreter list, the run carried a script whose digest is on the script allowlist.
- **Under these hypotheses:** The configuration `Env` is arbitrary (digest function, writable paths, noexec mounts, program allowlist, interpreter list, script allowlist, path allowlist, admin list): no condition on it at all. The initial files and the trace are arbitrary. The only conditions are structural: initial state has an empty run list and is not halted; the checks are `full`. Model conditions only; the world assumptions (complete mediation, fd-pinned hashing, honest usefulness, credential separation) are not hypotheses of the theorem and are not proved.
- **Does NOT say:** (1) That a real process with a non-allowlisted binary cannot run: only that the model's gate never records one, so every real exec path must go through that gate (complete_exec_mediation). (2) That an interpreter is recognised as one unless the environment lists its digest in the interpreter list: an allowlisted interpreter missing from that list runs any script. (3) That allowlisted programs are harmless, or that honest tasks can run (an empty allowlist satisfies the statement).
- **Kind:** general theorem (induction over the trace; it is `safe_of_sound` at the `full` configuration).

### Claim 2
## `ControlStack.SC08.safe_of_sound`

- **Says (plain English):** The same safety statement for any configuration of checks in which the digest check and the script check are turned on, whatever the other two checks (noexec mount, halt) are set to: after any trace from any initial files with no runs, every recorded run has an allowlisted program digest and, for interpreters, an allowlisted script digest.
- **Under these hypotheses:** `Sound C`: the digest switch is on and the script switch is on. Nothing else about the switches, the environment, the initial files or the trace. Model condition only.
- **Does NOT say:** (1) That the noexec or halt checks are unnecessary in the real system (it shows only that this one property does not need the noexec check; `sc08_safe` is its `full` instance and the file calls the noexec check "defence in depth"). (2) Anything about path-based allowlisting (the digest switch must be on). (3) Anything about the real digest function or the real loading path.
- **Kind:** general theorem.

### Claim 3
## `ControlStack.SC08.halt_freezes`

- **Says (plain English):** If the model state is already halted, then in the `full` configuration any further sequence of operations leaves the entire state exactly unchanged: no file write takes effect, nothing more runs, and the halted flag stays set.
- **Under these hypotheses:** The state is halted; the configuration is `full` (in particular the halt check is on). The environment and the trace are arbitrary. Model conditions only.
- **Does NOT say:** (1) That a halt is ever issued or processed (the halt operation only works if the caller number is on the admin list; no liveness is claimed). (2) That programs already started before the halt stop running: the model has no notion of a running process, only of exec requests being recorded. (3) Anything about the world outside the model state.
- **Kind:** general theorem (the "frozen once halted" check is built into `step`, so the proof is a short induction: close to definitional).

### Claim 4
## `ControlStack.SC09.sc09_safe`

- **Says (plain English):** Starting from the empty state (no processes, no grants, no recorded uses, not halted) and running any sequence of operations with the `full` checks, two things hold. First, every capability that any process holds belongs to a pair (lineage, capability) that appears in the grant table, which only grows when an operation claiming an admin identity issues a grant. Second, every recorded privileged use is either by a lineage that was granted that capability, or goes through an elevation rule in the trusted rule list whose binary and arguments match the recorded ones exactly and whose capability is the one used.
- **Under these hypotheses:** The policy `P` (admin list, elevation rule list, file-capability table) is completely arbitrary, including arbitrary elevation rules. The trace is arbitrary, with arbitrary caller numbers (so an operation may claim to be an admin; the theorem then treats it as a real admin act). The checks are `full`. Model condition only; kernel enforcement, admin separation and credential separation are not hypotheses.
- **Does NOT say:** (1) That the agent never obtains a capability: it holds whatever an op claiming an admin identity grants. (2) That any elevation rule is safe: an elevation rule applies to any live process of any lineage (the elevation clause does not check that the lineage was entitled to that rule), and rules are trusted by assumption. (3) That the real kernel cannot be bypassed, or that the list of recorded uses is all the privileged actions that really happen.
- **Kind:** general theorem (induction over the trace from `init`).

### Claim 5
## `ControlStack.SC09.spawn_attenuates`

- **Says (plain English):** In one spawn step in the `full` configuration, from a non-halted state where the parent process exists and the child number is unused, any process that appears in the new state but not in the old one (that is, the child) has the same lineage as the parent and a capability list that is a sub-collection of the parent's capability list at that moment.
- **Under these hypotheses:** The state is not halted; the parent `p` is found with record `q`; the child number `ch` is not already in use; the list of capabilities to keep (`keep`) is arbitrary. These are conditions on one state, not on traces.
- **Does NOT say:** (1) Anything about a multi-step trace; trace-level control of capabilities is `sc09_safe`. (2) That a child cannot later receive more capabilities (an admin `grant` can add them; the grant table is what bounds it). (3) Anything when the child number is already in use or the parent is missing (then no child is created).
- **Kind:** general theorem (one-step property; follows almost directly from the definition of spawn, which filters the parent's capabilities by `keep`).

### Claim 6
## `ControlStack.SC09.halt_freezes`

- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace leaves the whole state unchanged: no new process, grant or privileged use.
- **Under these hypotheses:** The state is halted; the checks are `full` (including the halt check); the policy and the trace are arbitrary. Model condition only.
- **Does NOT say:** (1) That a halt is ever triggered or processed (liveness). (2) That processes already running stop or lose capabilities in the real OS. (3) Anything about operations outside the model.
- **Kind:** general theorem (frozen-after-halt is built into `step`; short induction, close to definitional).

### Claim 7
## `ControlStack.SC10.sc10_safe`

- **Says (plain English):** From the empty initial state, after any trace of policy writes, cache refreshes, decisions, edits to the agent-writable policy file and search path, builds and halts in the `full` configuration: every recorded decision cited the latest stored policy version at that moment and that version was admin-written; and every recorded build used something whose digest equals the pinned digest.
- **Under these hypotheses:** The pinned location has the pinned digest (`hpin`, a world assumption stated as a hypothesis); arbitrary trace and caller numbers; configuration `full` (admin-only writes, fresh decisions, single evaluator, pinned-path builds, halt check all on).
- **Does NOT say:** (1) That the build toolchain is the pinned one in reality: the build record is the pinned location itself, so the toolchain conclusion is `hpin` restated; the agent-writable search path (`writePath`) is ignored by `full` because the `pinnedPath` switch routes builds to the pinned location. (2) Anything about container mounts or the host file system: only the abstract policy log and build digests exist in the model. (3) Anything about a compromised compiler at the pinned digest (the scenario excludes it).
- **Kind:** general theorem; the build part is definitional/trivial given `hpin`.

### Claim 8
## `ControlStack.SC10.policy_admin_only`

- **Says (plain English):** After any trace from the empty state in the `full` configuration, every stored policy version was written by a caller on the admin list.
- **Under these hypotheses:** The pinned location has the pinned digest (carried, not used for this conclusion); arbitrary trace and caller numbers; configuration `full`.
- **Does NOT say:** (1) That a mount table or any host configuration is covered: the model stores opaque policy numbers with no meaning, and no mount-specific operation exists; the scenario's "mount/policy configuration changed by a non-admin" is covered only to the extent the real mount configuration is the store's content and only changes through it. (2) That the writer is really an admin (identity is a claimed number). (3) That an admin's change is correct.
- **Kind:** general theorem (the admin check is built into the step; close to definitional).

### Claim 9
## `ControlStack.SC10.halt_freezes`

- **Says (plain English):** If the state is already halted, then in the `full` configuration no further operation changes the state: no new policy version, decision or build.
- **Under these hypotheses:** The state is halted, the configuration is `full` (halt check on); the environment and trace are arbitrary.
- **Does NOT say:** (1) That a halt is ever issued or processed, or that the real firewall stops enforcing or freezes on halt. (2) That decisions or builds already in flight are stopped. (3) Anything about the real policy store beyond the model's state.
- **Kind:** general theorem (the freeze is built into `step`; short induction, close to definitional).

### Claim 10
## `ControlStack.SC12.sc12_safe`

- **Says (plain English):** From the empty state, after any trace of session starts, registered spawns, bypass attempts, firings, session ends and halts, in the `full` configuration: every live entity is registered, and the session it truly descends from (its ghost "origin") is currently active and has never ended. So nothing belonging to a session that has ended is live.
- **Under these hypotheses:** The admin list is arbitrary; the trace is arbitrary, including arbitrary claimed session labels for spawns and bypass attempts. The configuration is `full`: creation only through the registry (so `bypass` does nothing), the child's session label is taken from the parent (the child's claimed label is ignored), ending a session revokes its whole registered lineage, and the halt check is on. Model conditions; the world assumptions (registry_complete, revocation_effective) are not hypotheses.
- **Does NOT say:** (1) That nothing escapes in a real system: unregistered creation paths (cron, systemd timers, cloud jobs, credentials) are excluded only by the `registryOnly` switch, i.e. by assumption. (2) That anything the agent did while the session was live is undone (the scenario scope excludes it). (3) That revocation really kills the real process or job.
- **Kind:** general theorem (induction over the trace).
