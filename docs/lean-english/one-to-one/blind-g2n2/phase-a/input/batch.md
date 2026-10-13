# English statements under test

### Claim 1
## `ControlStack.SC12.no_fire_after_end`

- **Says (plain English):** Take any state satisfying the model's invariant in which session `sess` is already in the ended list. Then after any further trace in the `full` configuration, the log of job firings restricted to jobs whose true lineage is `sess` is exactly what it was before: no new firing of any job of that lineage ever occurs.
- **Under these hypotheses:** The state satisfies the invariant `Inv` (every live entity registered with its label equal to its origin and origin active; active and ended lists disjoint; every earlier firing recorded before its lineage ended). `Inv` holds from the empty state by the model's own lemmas but is stated here for an arbitrary invariant state. The session is in the ended list. The configuration is `full`; the trace is arbitrary.
- **Does NOT say:** (1) That firings before the end did not happen or were harmless (the log of earlier firings is unchanged, not empty). (2) That a real cron/timer/cloud job cannot fire: only registered jobs are modelled (registry_complete). (3) That a halt always lands: it covers sessions already in the ended list, which includes every active session after a halt.
- **Kind:** general theorem.

### Claim 2
## `ControlStack.SC12.halt_freezes`

- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace leaves the entire state unchanged: no new session, helper, job or firing.
- **Under these hypotheses:** State halted; configuration `full` (halt check on); admin list and trace arbitrary.
- **Does NOT say:** (1) That a halt is issued or processed (liveness). (2) That already-running real processes stop (the halt removes registered live entries from the model's list; revocation_effective is a premise). (3) Anything outside the model state.
- **Kind:** general theorem (every operation is a no-op once halted by construction; close to definitional).

### Claim 3
## `ControlStack.AuthInstances.sc12_safe_authenticated`

- **Says (plain English):** Run the SC-12 model so that each operation carries a true issuer number and an operation that claims an identity (session start, session end, halt claim the caller; spawn, bypass and fire claim no identity) is applied only if the claimed identity equals the issuer; otherwise it is dropped. Then, for any trace of (issuer, operation) pairs: the same safety property as `sc12_safe` holds (every live entity registered, its origin session active and not ended), and for every live entity there is, in the trace, an operation issued by some admin `c` (not in `U`) of the form "start session with this entity's origin number" claiming `c`.
- **Under these hypotheses:** The admin list is arbitrary; `U` is any list of numbers none of which is on the admin list (this is the only hypothesis, a statement about how `U` was chosen); the trace is arbitrary. Model condition only. The real-world premise that the issuer number is the genuine platform-reported identity (and that the agent can only issue as members of `U`) is not in Lean; the theorem does not require that all agent operations carry issuers in `U`.
- **Does NOT say:** (1) That the issuer number is authentic: that is the residual premise (platform identity equals true issuer). (2) That spawns, bypass attempts and firings are authenticated (they claim no identity and are applied for any issuer). (3) The "not issued by `U`" conclusion is immediate from the admin-list membership and the hypothesis on `U`, so it carries no extra content beyond "an admin-claimed start operation, issued by that admin, exists in the trace".
- **Kind:** refinement/bridge (reduces the claimed-identity premise to an issuer-authenticity premise; first conjunct is `sc12_safe` transported through the authenticated run).

### Claim 4
## `ControlStack.AuthInstances.forged12_spawns_without_auth`

- **Says (plain English):** A concrete example with admin list containing only 9, in which agent 1 issues two operations, "start session 5 claiming to be admin 9" and "spawn helper job 6 from entity 5". If no authentication is applied (no operation claims any identity), both are applied and two entities are live. If the SC-12 claims are authenticated, both operations do nothing (the start claim by issuer 1 for admin 9 is dropped, and the spawn then finds no entity 5) and nothing is live.
- **Under these hypotheses:** None beyond the concrete example (admin list [9], `full` configuration, the two-operation trace `forged12`).
- **Does NOT say:** (1) That authentication is sufficient (it is one concrete trace, not a general result). (2) That real identity authentication exists. (3) That other forgeries are caught.
- **Kind:** negative control (shows that without the authentication guard the forged admin claim succeeds), proved by `decide`.

### Claim 5
## `ControlStack.AuditDispatch.trace_safe`

- **Says (plain English):** Take any state in which every recorded effect id also appears in the audit list and the effect list has no duplicates. After any sequence of the model's operations (request, app event, app schema, dispatch, crash, restart), the final state again has: every effect id appears in the audit list, no effect id is repeated; and the old audit list is an initial segment of the new one (audits are append-only).
- **Under these hypotheses:** The starting state satisfies the invariant (every effect has an audit entry; effects have no duplicates). The model's dispatch step is enabled only for an id that was requested and not yet effected, and appends the audit then the effect for that id together. No condition on who issues which operation.
- **Does NOT say:** (1) That the audit was written before the effect in time: this theorem states only that the effect's id is in the audit list at the end (ordering within one step is a separate lemma, `dispatch_audit_first`, not part of this theorem). (2) That an agent cannot disable or alter the audit path in a real system (append-only is a property of the model's operations, not of real database privileges, which the file says are tested separately). (3) Anything about completion-time auditing or about real workflow execution happening only through the dispatcher.
- **Kind:** general theorem (induction over the trace).

### Claim 6
## `ControlStack.AuditDispatch.app_cannot_effect`

- **Says (plain English):** For any state and any operation that is not a dispatch, the effect list after the step is the same as before.
- **Under these hypotheses:** The operation is not a dispatch operation for any id (so it is one of request, app event, app schema, crash, restart).
- **Does NOT say:** (1) That the real application cannot cause a real effect: the model defines the app's capabilities as the non-dispatch operations, and the file states that real exclusivity depends on PostgreSQL privileges and the broker/worker credentials being the dispatcher's alone. (2) That the app cannot choose what gets dispatched: a `request id` from the app makes any id eligible for the dispatcher. (3) That `dispatch` is only called by the trusted party.
- **Kind:** definitional/trivial (proved by case analysis on the operation; the model's non-dispatch operations are defined not to touch the effect list).

### Claim 7
## `ControlStack.SC14.sc14_safe`

- **Says (plain English):** Start from an empty ledger (nothing spent, clock 0, any chosen expiry) and run any trace of work steps, clock ticks, admin expiry changes and halts that does not contain a storage rollback. In the `full` configuration: the sum of the actual usage vectors of all admitted work is within the cap, resource by resource (compute, tokens, network); in every time window (the stretch between ticks) the sum of actual usage is within the per-window rate limit, resource by resource; and every admitted work step happened at a clock time before the expiry that was in force when it ran.
- **Under these hypotheses:** Caps, rates and admin list are arbitrary. The trace contains no rollback operation (the "legal" premise, which is the anti-rollback assumption). The "actual usage" attached to each work step is the metered value; the agent's own report is ignored. Refused work (one that would exceed a cap, rate or expiry) is not recorded and is treated by the model as consuming nothing. Expiry can be changed only by an operation claiming an admin identity. Model conditions only; trusted meter, trusted clock and credential separation are not hypotheses.
- **Does NOT say:** (1) That real consumption is within caps: the usage numbers are whatever the operation labels "actual"; a resource the meter does not see (or work refused by the gate but run anyway) is outside the model (trusted_meter). (2) A real-time rate bound: a window ends only when a `tick` operation occurs, and ticks are arbitrary trace operations; real-time rates need the clock premise. (3) That the expiry is the intended one: an operation claiming an admin identity can move it (credential separation).
- **Kind:** general theorem (inductive invariant over the trace).

### Claim 8
## `ControlStack.SC14.halt_freezes`

- **Says (plain English):** If the state is already halted, then in the `full` configuration any further trace of operations (including a rollback) leaves the list of usage records unchanged: no work is admitted after a halt.
- **Under these hypotheses:** The state is halted; configuration `full`; the trace is arbitrary and need not be rollback-free. The conclusion concerns only the usage list (the spent counter may still be reset by a `rollback` operation).
- **Does NOT say:** (1) That the whole state is frozen (only the usage record list is; a rollback can still reset the spent counter, which does not matter for the usage list). (2) That a halt is ever issued or processed. (3) That real work already running stops.
- **Kind:** general theorem (once-halted checks are built into `step`; short induction, close to definitional).
