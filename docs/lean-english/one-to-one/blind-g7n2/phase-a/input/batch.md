# English statements under test

### Claim 1
## `ControlStack.SC28.sc28_safe`

- **Says (plain English):** Start from the empty system (no leases, assignments, revocations, ledger, usage; not halted). Run any list of operations (admin issue of leases, assignment of workers to leases, fork of a worker (child joins its parent's lease), revoke, work steps with an agent-chosen actual consumption and agent-reported cost, restart, halt) as long as none is a storage rollback. Then: (i) the sum of actual units in the usage log is at most the global cap G; (ii) for each lease id, the sum of actual units charged under that lease is at most that lease's budget (0 if the lease does not exist); (iii) the number of accepted work steps is at most G. This holds for every choice of admin list and every G.
- **Under these hypotheses:** Model conditions (not world facts): the gate charges each accepted step the larger of the actual units and 1 (the meter is trusted: the agent's reported cost is ignored); a work step is accepted only if the worker holds an unrevoked lease whose remaining budget covers the charge and the global remaining cap covers the charge; a step that is not accepted adds nothing to the usage log; forks give the child the parent's lease; no operation in the trace is a rollback. World assumptions hidden in these: that the real meter sees every unit consumed by every descendant, that a refused step really does no consuming, that identities in `issue`/`revoke`/`halt` are the admins' own acts (credential separation), and that the ledger is not rolled back.
- **Does NOT say:** It does not say anything about consumption that does not go through an accepted `work` operation (unmetered consumers, work performed before the gate decision, or refused work that nonetheless ran). It does not say that real usage equals the charged amount, only that the model's usage log is what the model records and the charge is at least that. It does not say honest agents get to finish work (a shared cap can starve them: see `global_cap_blocks_honest`), nor does it cover rollback (excluded by hypothesis).
- **Kind:** general theorem (induction over the trace)

### Claim 2
## `ControlStack.SC28.revoked_lease_stops`

- **Says (plain English):** For any configuration of checks (including weakened ones), any state in which a lease id is already in the revoked list, and any further sequence of operations (including rollbacks), the total actual usage recorded under that lease id is the same at the end as it was at the start.
- **Under these hypotheses:** The lease id is in the revoked list of the starting state (starting state need not be reachable). A work step is accepted only if its lease is not revoked, in every configuration; revocation is never undone (the revoked list only grows). The only sense of "revoke" here is bookkeeping in the model; that a real revoke kills the processes is a refinement matter (see `concrete_revoked_stops`).
- **Does NOT say:** It does not say the worker or its children stop consuming: a worker can be re-assigned (by an admin) to another lease and consume there, and a child already on another lease is unaffected. It does not say the consumption stops outside the metered model. Note the statement concerns the usage log, and rollback does not alter the usage log.
- **Kind:** general theorem (induction; short case analysis per step)

### Claim 3
## `ControlStack.SC28.fork_shares_lease`

- **Says (plain English):** In the full configuration, if the system is not halted, the parent worker holds lease `lid`, and the child worker has no assignment yet, then after a fork operation of that parent and child (any caller, any fresh-lease id argument), the child's lease is `lid`.
- **Under these hypotheses:** Not halted; parent assigned to `lid`; child not already assigned; the descendant-attribution (share) check is on. The fork operation does not check who the caller is, so any identity may trigger it in the model.
- **Does NOT say:** It does not say the child can consume (the lease may be revoked or exhausted), that every real descendant gets a fork operation recorded (a process that escapes the fork accounting is outside the model; the refinement relies on a kernel premise that a child lands in its parent's cgroup), or that a child already assigned elsewhere is moved.
- **Kind:** general theorem (essentially unfolds the fork definition; nearly definitional)

### Claim 4
## `ControlStack.SC28.halt_freezes`

- **Says (plain English):** If the system is already halted, then after any further sequence of operations (even rollbacks) the usage log is exactly as it was before.
- **Under these hypotheses:** Halted flag true in the starting state (not required to be reachable); full checks (halt check on). The halted flag can be set only by a halt operation from an admin (a model condition; admin credential secrecy is a world assumption).
- **Does NOT say:** It does not say the ledger or other state is frozen (a rollback operation still changes the ledger), that real processes are stopped, or how quickly after halt consumption ends.
- **Kind:** general theorem

### Claim 5
## `ControlStack.AuthInstances.sc28_safe_authenticated`

- **Says (plain English):** Operations now come as pairs (true issuer, operation). An operation that claims an identity (every operation except restart and rollback; `work w` claims worker w) is applied only if its issuer equals the claimed identity; otherwise it is dropped. For any list of such issued operations in which no operation at all is a rollback and the adversary's issuers are not admins: (i) the same three budget bounds as `sc28_safe` hold on the final state; (ii) every lease present in the final state was created by an issue operation that appears in the trace issued by an admin who is not an adversary issuer; (iii) every revoked lease was revoked by a revoke operation issued by such an admin.
- **Under these hypotheses:** World assumption: the "true issuer" recorded with each operation is the real authenticated identity (e.g. OS-reported), and the adversary's issuers (the set U) are disjoint from the admin list (credential separation). Model condition: no rollback among the operations (all operations, applied or not). Part (i) does not use the set U at all.
- **Does NOT say:** Part (i) is `sc28_safe` applied to the applied sub-trace, so authentication adds nothing to the budget bound itself: it holds for forged traces too (`forged28_consumes_without_auth` shows the harm of forging is an unauthorized grant, not a budget violation). The conclusion does not mention assignment or halt operations, so it does not state that assignments were admin-issued, though the guard also applies to them. It does not prove the platform's identity is the true issuer.
- **Kind:** general theorem (instance of a generic authenticated-log lemma; part (i) is a restatement via `authRun_eq`)

### Claim 6
## `ControlStack.AuthInstances.forged28_consumes_without_auth`

- **Says (plain English):** With admin 9 and global cap 1000, consider agent 1 issuing three operations: a lease issue claiming to be admin 9, an assignment claiming to be admin 9, and its own work step. If claims are never checked, the lease is created, worker 1 is assigned, and 5 units are recorded as consumed under lease 0. If claims are checked against the issuer, the forged operations are dropped and nothing is consumed.
- **Under these hypotheses:** None; a closed computation.
- **Does NOT say:** It does not show a budget bound is violated in the unauthenticated case (5 is within lease 0's budget of 100 and the cap); it shows an unauthorized grant. It is one example, not a general necessity result.
- **Kind:** negative control (shows a weakened model fails) / finite computation

### Claim 7
## `ControlStack.SC28Liveness.honest_steps_progress`

- **Says (plain English):** If the system is not halted, a worker has an unrevoked lease with budget b, and the total gate charge of a list of honest work units (reported equals actual; charge is the larger of the unit and 1) fits both within the lease's remaining budget and within the remaining global cap, then running those work steps one after another accepts every one of them, and the usage log grows by exactly those entries.
- **Under these hypotheses:** Not halted, worker assigned to a lease that exists and is unrevoked, remaining lease budget at least the total charge, remaining global cap at least the total charge. No other agent acts in between (a straight sequence, no interleaving).
- **Does NOT say:** It does not say real honest jobs fit their leases or get completed (the "honest_usefulness" premise); it does not cover interleaving with other agents (that is `progress_interleaved`); it assumes the worker's charges equal what it reports.
- **Kind:** general theorem

### Claim 8
## `ControlStack.SC28Liveness.progress_interleaved`

- **Says (plain English):** Suppose a work step by worker w with units a would be admissible in state s (the lease exists, the charge fits the lease's remaining budget and the global remaining cap). After any sequence of other operations p, the same work step is either accepted in the new state, or one of these holds in the new state: the system is halted; the lease is revoked; the worker is no longer on that lease; the lease's spending has gone up since s; or the global spending has gone up since s.
- **Under these hypotheses:** The step is admissible at the starting state (lease/budget/cap conditions as above; one hypothesis about the worker's lease is unused, marked by an underscore). The interleaved operations are arbitrary (rollbacks allowed). Model conditions: gate charges max of actual and 1.
- **Does NOT say:** It is a weak liveness claim: the escape clause "the global spending has gone up" is triggered by any other agent's accepted work step, so in a busy system the disjunction holds trivially and guarantees nothing. It does not show honest jobs complete, nor any bound on how often an honest step is blocked.
- **Kind:** general theorem

### Claim 9
## `ControlStack.SC28Liveness.global_cap_blocks_honest`

- **Says (plain English):** In a concrete run with admin 9 and global cap 10, two leases of budget 10 each, worker 1 on lease 0 and worker 2 on lease 1, worker 2 consumes all 10 units. Then worker 1's step of 1 unit is refused even though lease 0 has been entirely unspent; the usage log shows only worker 2's 10 units.
- **Under these hypotheses:** None; a closed computation.
- **Does NOT say:** It does not say this is a flaw or fix; it prices availability. It shows a shared global cap can deny honest work (denial of service by another agent), which the safety theorem does not prevent.
- **Kind:** negative control (shows a weakened model fails), in the availability sense; finite computation

### Claim 10
## `ControlStack.AntiRollback.sc28_rollback_safe`

- **Says (plain English):** For SC-28 with any admin list and any global cap G: after any sequence of operations that mixes legal SC-28 writes, commits, crashes/restarts and rollbacks of the stored counters to any earlier backup, the released usage log equals the usage log of the plain legal SC-28 run of exactly the committed operations, and that plain run satisfies the same three budget bounds as `sc28_safe` (total at most G; each lease within its budget; at most G work steps).
- **Under these hypotheses:** The anchor premises of `rollback_transfer` (trusted monotonic anchor, record integrity, write-then-increment protocol) as model conditions; the SC-28 operations themselves are the legal ones only (no SC-28-level rollback operation, but the storage rollback is now an adversary move). Same SC-28 model premises as `sc28_safe` (trusted meter, credential separation).
- **Does NOT say:** It bounds what is released (committed) and nothing about work done in the window between a write and its commit, when the real consumption may already have happened (effects are modelled as occurring only on release). It does not say the gate stays available under rollback (the gate fails closed and halts). It does not say the anchor is trustworthy.
- **Kind:** refinement/bridge (instance of `rollback_transfer`)

### Claim 11
## `ControlStack.SC28Refinement.concrete_safe`

- **Says (plain English):** In a concrete cgroup-controller machine (a controller creates leases, launches processes into a lease's cgroup before they run, processes fork into their parent's cgroup, processes consume units that the kernel charges to the lease and to the whole run, the controller can revoke a lease (killing its processes) or halt), for any trace whatsoever (including processes launched with no placement), the kernel's counters satisfy: total accounted at most G, each lease counter at most its limit (0 if no lease), and at most G accounted consumption events.
- **Under these hypotheses:** None on the trace. Model conditions that stand in for world premises: the kernel refuses a consume that would exceed the lease limit or the run's cap (hierarchical enforcement, built into the consume rule as a refusal); a forked child is in its parent's cgroup (fork inherits); revoke and halt atomically kill the affected processes; the controller is a trusted root and counters survive for the run. The result is proved by simulating the machine in the SC-28 model and using `sc28_safe` (controller identity 0 as the only admin).
- **Does NOT say:** It does not prove the kernel enforces limits or that fork inheritance holds: these are rules written into the machine, so the theorem is a consistency check of the bookkeeping, not evidence about the kernel. The counters count only consumption by placed processes; consumption by unplaced processes is recorded separately and unconstrained (`unplaced_invisible`: 100 units consumed with G = 10 while this theorem still holds). Counters are the same list as the "usage", so the bound on actual versus charged is true by construction.
- **Kind:** refinement/bridge

### Claim 12
## `ControlStack.SC28Refinement.concrete_revoked_stops`

- **Says (plain English):** In the concrete controller machine, if a lease id is in the revoked list after some first part of a trace, then after running any second part, the kernel counter for that lease is the same as it was after the first part.
- **Under these hypotheses:** The lease id is in the revoked list after the first part. Model conditions: revoke kills all live processes in the lease's cgroup; a dead process cannot fork or consume; launching into a revoked lease is refused by the controller; a child lands in its parent's cgroup. These are rules of the machine (world premises about the kernel and the controller), not derived.
- **Does NOT say:** It does not say that the kill is instantaneous or reliable against adversarial workloads racing it (the kill is an atomic step here; the runtime measured termination within about one second on benign workloads), or that processes outside the lease's cgroup (unplaced ones) stop.
- **Kind:** refinement/bridge

### Claim 13
## `ControlStack.SC28Refinement.exclusive_placement_safe`

- **Says (plain English):** In the concrete controller machine, for any trace that contains no operation that launches an unplaced process (one that starts outside the run's cgroup), no consumption occurs outside the run's cgroup, and the real total (the run's accounted counter plus all unaccounted consumption) is at most G.
- **Under these hypotheses:** The trace has no unplaced launches. This is the world assumption of exclusive placement: every process that consumes descends from a controller launch with placement. In this model there is no operation that moves a process out of its cgroup, so once all launches are placed, escape is impossible by construction.
- **Does NOT say:** It does not show that real processes cannot escape their cgroup, be launched without placement, or consume off-meter by some other route (those are outside the machine's alphabet, so the model cannot even express them); it does not cover GPUs, network or other resource kinds. "Real total" means total in this model (accounted plus the model's unplaced bucket).
- **Kind:** refinement/bridge (the content is largely the exclusion hypothesis; the rest is `concrete_safe`)
