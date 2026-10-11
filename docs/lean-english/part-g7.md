# Plain-English statements, part G7 (SC-27 and SC-28)

Paths below are relative to `ControlStack/`. All files were read in full for the declarations named; none contains `sorry`, a user `axiom`, or `native_decide` (grep). I did not run Lean, so "proved" below means "the Lean source states and (per the file) proves", not independently rechecked.

---

# SC-27: Tampered evidence and assurance manifests  (status: CONDITIONAL)

**Harm.** A verifier accepts a manifest whose evidence log is not exactly a log that an independent witness anchored (the log was modified, reordered, truncated or extended after anchoring).

**Adversary / scope.** A writer that can append, rewrite its whole log storage, publish heads of its own, and choose when anchoring and verification happen and which manifests are submitted. Lean model only; runtime evidence is a single-host, benign-workload, one-UID reference run.

**What the Lean claims, taken together, and what they leave to assumptions.** The Lean shows that, in an abstract event machine, a verifier that accepts a manifest only when its hash-chain head equals a head recorded by the independent witness (not the writer's own heads, not current storage) can only ever accept a list that the witness anchored at some point, provided the hash chain head is collision-free on the lists that actually occur in that run. The extension-only variant adds that every later anchor extends every earlier anchor, so a rewrite made after anchoring can never itself become anchored. What is left open: (a) all of this protects entries only once anchored (a rewrite before the first anchoring is anchored and accepted, `rewrite_before_anchor_window`); (b) "anchored" does not mean "true" and does not mean "the newest log": the verifier will still accept an older anchored prefix (truncation back to an earlier anchor) and any fabricated entries the writer appended before the next anchoring; (c) the witness independence, the anchor-service integrity, the hash collision resistance on the run's lists, and how soon anchoring happens are assumptions, not theorems; (d) the Python-to-machine link is tested only, and a known gap (silence on truncation to empty) exists in the run-1 witness.

**World assumptions (from the scenario):**
- `independent_anchor` (NOT_PROVED): an independently administered witness records heads, not the writer.
- `hash_injective_on_run` (NOT_PROVED): chain head is injective on accepted/anchored logs (collision resistance).
- `anchor_frequency` (NOT_PROVED): anchoring happens soon enough that the pre-anchor window is acceptable.
- `model_runtime_correspondence` (THEOREM_VERIFIED for the machine-to-model link, TESTED for Python-to-machine): includes the recorded `empty_truncation_silent` finding.

---

### `ControlStack.SC27Chain.sc27_safe`  — `Scenarios/SC27Chain.lean:191`
- **Says (plain English):** Take any sequence of operations (writer appends, whole-log rewrites, anchoring by the independent witness, writer-published heads, verification requests, admin halts) run from the empty state with every check on. If the hash-chain head function never gives the same value to two different lists drawn from {manifests the verifier accepted} together with {logs the independent witness anchored}, then every accepted manifest is exactly equal to a log that the independent witness anchored at some earlier time.
- **Under these hypotheses:** (1) Model conditions (not world facts): the verifier's acceptance rule in `full` mode is "the manifest's chain head equals the head of some anchor entry that was recorded by the independent witness" (anchors the writer published itself are flagged and ignored; the "check current storage" and "anchored prefix plus extra suffix" shortcuts are switched off); the halt check is on. An anchoring step records the head of whatever the writer-controlled storage holds at that moment, together with a ghost copy of that list; the adversary chooses when anchoring happens. (2) A condition on the specific run: the chain head function is injective on the set of accepted manifests and independently anchored logs of the final state. This is the collision-resistance premise, stated per run, not globally; it is a world assumption for real hashes and not provable in Lean for a compressing hash.
- **Does NOT say:** It does not say the anchored log is genuine or untampered: the ghost "truth" list is not mentioned in the conclusion, and a rewrite made before anchoring is anchored and accepted. It does not say the accepted manifest is the latest anchored log: an older anchored log (truncation back to an earlier anchor) is accepted. It does not say anything about the writer's later-anchored tampered storage ("periodic anchoring launders a rewrite"; that is closed only in the extension-only model below).
- **Kind:** general theorem
- **Non-vacuity:** The hypothesis holds trivially for the empty trace (and is not shown for any nonempty trace). `honest_accept` in the same file shows a nonempty run in which a manifest is accepted, but it does not prove the injectivity hypothesis for that run, so for nonempty traces the hypothesis is NOT SHOWN to be satisfiable in Lean.
- **Read depth:** full

### `ControlStack.SC27Chain.tamper_after_anchor_detected`  — `Scenarios/SC27Chain.lean:251`
- **Says (plain English):** With the concrete toy hash (the new head is 100 times the old head plus the entry plus 1, starting at 0) and one admin, two specific runs end with no manifest accepted: (i) the writer appends 5, the witness anchors, the writer rewrites storage to [7], and a manifest [7] is submitted; (ii) the writer appends 5 then 6, the witness anchors, the writer reorders storage to [6,5], and a manifest [6,5] is submitted.
- **Under these hypotheses:** None beyond the concrete toy hash and the `full` checks; it is a closed computation. No assumption about real hashes is involved.
- **Does NOT say:** It is two examples, not a statement about all tamperings. It does not show that the honest manifest ([5], or [5,6]) is accepted in those runs (that is `honest_accept`), and it does not show that detection works for a hash with collisions (`collision_breaks` shows it fails).
- **Kind:** finite computation (decide/native)
- **Non-vacuity:** n/a (it is itself a concrete run; the model is the same one used by `honest_accept`, which shows acceptance in the honest case).
- **Read depth:** full

### `ControlStack.SC27Chain.halt_freezes`  — `Scenarios/SC27Chain.lean:212`
- **Says (plain English):** If the machine's halted flag is already set, then running any further sequence of operations (appends, rewrites, anchors, writer-published heads, verifications, further halts) leaves the entire state, including the list of accepted manifests, exactly unchanged.
- **Under these hypotheses:** Starting state is arbitrary (not required to be reachable) with the halted flag true; the halt check is on (`full`). Setting the flag is possible only through a halt operation by a caller in the environment's admin list; that is a model condition, and whether agents can obtain admin credentials is a world assumption not covered here.
- **Does NOT say:** It does not say that any trace can reach the halted state, that a real verifier process stops, or that halt happens promptly. It is a freeze of the model state only.
- **Kind:** general theorem (induction over the trace; the one-step lemma is a case split)
- **Non-vacuity:** NOT SHOWN as a theorem hypothesis; `no_halt_check_breaks` (same file) shows a run where a halt happens and the full-check machine accepts nothing afterwards.
- **Read depth:** full

### `ControlStack.SC27ExtensionOnly.sc27_ext_safe`  — `Scenarios/SC27ExtensionOnly.lean:159`
- **Says (plain English):** In the model where the witness anchors a new state only if the writer's current storage extends the witness's previously anchored state (otherwise it records a fork alarm and anchors nothing), if the chain head is injective on the accepted manifests and anchored logs of the final state, then every accepted manifest (a) is exactly some log the witness anchored, and (b) is a prefix of (or equal to) the witness's most recently anchored log.
- **Under these hypotheses:** Same per-run injectivity premise as `sc27_safe` (world assumption: collision resistance on the lists in play). Model conditions: the verifier accepts a manifest iff its chain head equals the head of some anchored log; the adversary chooses any appends, rewrites, anchoring times and manifests; there is no halt and no writer-published-head channel in this model. The witness's memory of "last anchored log" and the anchor log are outside writer control (an independence assumption built into the machine).
- **Does NOT say:** It does not say the accepted manifest is the newest anchor: any earlier anchored log (which is a prefix of the latest) is accepted, so truncation back to an earlier anchored state is NOT rejected. It does not say the anchored content is true: entries the writer appends (even fabricated) and anything it rewrites before the first anchoring get anchored on a later period. Part (b) is a direct consequence of (a) plus the anchors-form-a-prefix-chain invariant.
- **Kind:** general theorem
- **Non-vacuity:** Trivial for the empty trace. `honest_periods` (same file) shows a nonempty run where [5] and then [5,6] are accepted, but it does not prove the injectivity hypothesis; NOT SHOWN for nonempty traces.
- **Read depth:** full

### `ControlStack.SC27ExtensionOnly.tampered_never_anchored`  — `Scenarios/SC27ExtensionOnly.lean:173`
- **Says (plain English):** Start from any state that satisfies the model's invariant (anchors have correct heads, anchored logs form a prefix chain and are all prefixes of the last anchor, and every accepted manifest has a matching anchor), in which a log `l` is already anchored. Then, after running any further sequence of operations in the extension-only model, every anchor in the final state was either already there before, or is a list that extends `l`. In words: a list that does not extend an anchored log can never become anchored later.
- **Under these hypotheses:** The starting state satisfies the invariant (a model condition; every state reachable from the empty state satisfies it, as `run_inv` shows); `l` appears as the ghost copy of one anchor. No injectivity assumption is needed for this statement: it speaks about the anchored lists themselves, not heads.
- **Does NOT say:** It does not say the extending list is honest: the writer can append arbitrary entries and have them anchored. It does not say the first anchored state was genuine. It does not say no manifest of a tampered list is accepted: acceptance goes through heads, so that further needs collision resistance (it is covered by `sc27_ext_safe`).
- **Kind:** general theorem
- **Non-vacuity:** The empty initial state satisfies the invariant (`inv_init`), and `periodic_anchor_launders` / `honest_periods` give nonempty runs; the specific `l` existing is shown by the honest runs. Reasonably non-vacuous.
- **Read depth:** full

### `ControlStack.SC27ExtensionOnly.anchors_chain`  — `Scenarios/SC27ExtensionOnly.lean:149`
- **Says (plain English):** In the extension-only model, for any sequence of operations from the empty state, the logs anchored by the witness, in the order they were anchored, form a chain in which each is a prefix of every later one, and each anchored log is a prefix of the witness's recorded latest anchor.
- **Under these hypotheses:** None beyond the model (any appends, rewrites, anchor attempts, verifications). The extension-only check being on is part of the model, and the witness's memory and anchor log are assumed beyond the writer's reach.
- **Does NOT say:** It says nothing about whether the content is true, about what the verifier accepts (that is `sc27_ext_safe`), or about what happens if the witness's memory can be overwritten.
- **Kind:** general theorem (read off an inductive invariant)
- **Non-vacuity:** Holds trivially for empty anchors; nonempty chains are exhibited by `honest_periods`.
- **Read depth:** full

### `ControlStack.SC27ExtensionOnly.alarm_iff`  — `Scenarios/SC27ExtensionOnly.lean:214`
- **Says (plain English):** For any state, one anchoring attempt by the extension-only witness appends the current storage to the alarm list exactly when the current storage does not extend the last anchored state (a first anchoring, with no previous anchor, never alarms); and when it does not extend, the list of anchors is left unchanged.
- **Under these hypotheses:** Only the model definition of the witness step; no assumption about hashes (the model compares actual lists, not heads).
- **Does NOT say:** It does not say anyone reads or acts on alarms. It does not describe the real Python witness: the real witness compares heads, and the refinement file records that it is silent on truncation to empty (`empty_truncation_silent`), where this abstract model would alarm. It says nothing about alarms being tamper-proof.
- **Kind:** general theorem (case analysis on one step; close to a restatement of the witness step's definition)
- **Non-vacuity:** NOT SHOWN as a hypothesis question (no hypotheses beyond the type); `periodic_anchor_launders` shows a run where the alarm list is [[7]].
- **Read depth:** full

### `ControlStack.SC27Refinement.concrete_ext_safe`  — `Scenarios/SC27Refinement.lean:316`
- **Says (plain English):** In a more concrete machine that mirrors the runtime's events (writer appends, rewrites and self-published heads; witness examines storage, remembering only the length and head of its last anchor; verifier recomputes a manifest's head and accepts iff it matches a witness-recorded anchor head, not a writer-published head), every accepted manifest is a list that the witness anchored, and a prefix of the witness's latest anchor. This transfers `sc27_ext_safe` to that machine by a forward simulation.
- **Under these hypotheses:** Two world-type assumptions: (1) at every witness examine step, the chain head is injective on the pair (last anchored list, the same-length prefix of current storage) (`TraceInj`, collision resistance for the head comparison); (2) the chain head is injective on the accepted manifests and the anchored lists of the final state. Model conditions: the deployed verifier (`trustWriter = false`); the writer cannot modify the witness's memory or log; the verifier reads only the witness's log; fsync durability of the witness's log. The anchored lists in the conclusion are ghost copies kept by the model; the real witness stores heads and lengths.
- **Does NOT say:** It does not prove that the Python harness implements this machine (only tested, run-1). It does not rule out the recorded gap that the witness stays silent on truncation to empty (it only says nothing wrong is accepted). The "latest anchor" conclusion is only a prefix statement: an older anchored list is still accepted. It is not a statement about real SHA-256 beyond the two injectivity hypotheses.
- **Kind:** refinement/bridge
- **Non-vacuity:** Both hypotheses hold trivially for the empty trace. `honest_concrete` shows a nonempty accepted run but does not prove the hypotheses for it; NOT SHOWN for nonempty traces.
- **Read depth:** full

### `ControlStack.SC27Refinement.concrete_tampered_never_anchored`  — `Scenarios/SC27Refinement.lean:330`
- **Says (plain English):** In the concrete machine, split any trace into a first part and a second part. If a list `l` is among the witness's anchor records after the first part, then every anchor record in the log after both parts is either one that was already there after the first part, or is a list that extends `l`. So nothing that fails to extend an anchored list is anchored afterwards.
- **Under these hypotheses:** The injectivity condition at every examine step across the whole combined trace (`TraceInj`, collision resistance on the head comparison); deployed verifier setting; witness independence as above. No injectivity assumption on accepted lists is required here, only on the witness's own head comparisons.
- **Does NOT say:** It does not say what extends `l` is honest; it does not cover truncation to empty being alarmed (the witness is silent there, though nothing is anchored); it does not cover a rewrite before the first anchoring.
- **Kind:** refinement/bridge
- **Non-vacuity:** Trace-level injectivity is trivial for empty traces; for nonempty traces NOT SHOWN as a Lean hypothesis (the concrete witness `honest_concrete` is a computation, not an instance of this theorem).
- **Read depth:** full

---

# SC-28: Multiple agents individually within limits jointly exceed the overall budget  (status: CONDITIONAL)

**Harm.** Total consumption across agents and all their descendants exceeds the global budget, or a lease's lineage exceeds its own budget, or work continues after revocation or HALT. ("By X" means "by an operation carrying X's authenticated identity".)

**Adversary / scope.** Model: any trace of issue, fork, work, revoke, restart and halt operations (storage rollback excluded unless the anti-rollback layer is used). Runtime: benign workloads only on a single host with cgroup v2 (CPU time and pids); no adversarial workloads, GPUs, network or token spend, multi-host budgets.

**What the Lean claims, taken together, and what they leave to assumptions.** In the joint budget model, after any trace of operations (no rollback), the actual units consumed by accepted work steps are within the global cap, within each lease's budget (a forked child shares its parent's lease), and the number of accepted steps is at most the cap; revoked leases stop growing and HALT freezes everything; this transfers to an event-level cgroup controller machine and also holds when storage rollback is allowed but a trusted monotonic anchor exists. What remains assumptions: the charge for each accepted step is at least the actual usage (a trusted meter that sees every unit of consumption, including by descendants), a step the gate refuses consumes nothing, kernel enforcement and fork inheritance are built into the concrete machine as rules rather than proved from a kernel, exclusive placement (no process consuming outside the run's cgroup) is a hypothesis of the one theorem about real totals, credential separation is only reduced to "issuer authenticity", and honest availability is only shown in the weak form below.

**World assumptions (from the scenario):**
- `credential_separation` (NOT_PROVED): trusted-role identities cannot be forged by agents; reduced to issuer authenticity in `sc28_safe_authenticated`.
- `trusted_meter` (NOT_PROVED): the meter sees every unit of consumption by every descendant.
- `anti_rollback` (THEOREM_VERIFIED, reduced): ledger never rolled back; reduced to a trusted monotonic anchor in `AntiRollback`.
- `adversarial_workloads` (NOT_PROVED): the mechanism holds against workloads that try to evade accounting or termination.
- `honest_usefulness` (NOT_PROVED): honest jobs complete within their leases; formal counterpart is `SC28Liveness`.
- `model_runtime_correspondence` (THEOREM_VERIFIED for the controller-to-model link, TESTED for Python meter-to-controller).

---

### `ControlStack.SC28.sc28_safe`  — `Scenarios/SC28Budget.lean:294`
- **Says (plain English):** Start from the empty system (no leases, assignments, revocations, ledger, usage; not halted). Run any list of operations (admin issue of leases, assignment of workers to leases, fork of a worker (child joins its parent's lease), revoke, work steps with an agent-chosen actual consumption and agent-reported cost, restart, halt) as long as none is a storage rollback. Then: (i) the sum of actual units in the usage log is at most the global cap G; (ii) for each lease id, the sum of actual units charged under that lease is at most that lease's budget (0 if the lease does not exist); (iii) the number of accepted work steps is at most G. This holds for every choice of admin list and every G.
- **Under these hypotheses:** Model conditions (not world facts): the gate charges each accepted step the larger of the actual units and 1 (the meter is trusted: the agent's reported cost is ignored); a work step is accepted only if the worker holds an unrevoked lease whose remaining budget covers the charge and the global remaining cap covers the charge; a step that is not accepted adds nothing to the usage log; forks give the child the parent's lease; no operation in the trace is a rollback. World assumptions hidden in these: that the real meter sees every unit consumed by every descendant, that a refused step really does no consuming, that identities in `issue`/`revoke`/`halt` are the admins' own acts (credential separation), and that the ledger is not rolled back.
- **Does NOT say:** It does not say anything about consumption that does not go through an accepted `work` operation (unmetered consumers, work performed before the gate decision, or refused work that nonetheless ran). It does not say that real usage equals the charged amount, only that the model's usage log is what the model records and the charge is at least that. It does not say honest agents get to finish work (a shared cap can starve them: see `global_cap_blocks_honest`), nor does it cover rollback (excluded by hypothesis).
- **Kind:** general theorem (induction over the trace)
- **Non-vacuity:** `honest_trace_works` shows a nonempty legal run with accepted work. The only hypothesis is the legal-trace condition, which the empty trace and honest traces satisfy.
- **Read depth:** full

### `ControlStack.SC28.revoked_lease_stops`  — `Scenarios/SC28Budget.lean:326`
- **Says (plain English):** For any configuration of checks (including weakened ones), any state in which a lease id is already in the revoked list, and any further sequence of operations (including rollbacks), the total actual usage recorded under that lease id is the same at the end as it was at the start.
- **Under these hypotheses:** The lease id is in the revoked list of the starting state (starting state need not be reachable). A work step is accepted only if its lease is not revoked, in every configuration; revocation is never undone (the revoked list only grows). The only sense of "revoke" here is bookkeeping in the model; that a real revoke kills the processes is a refinement matter (see `concrete_revoked_stops`).
- **Does NOT say:** It does not say the worker or its children stop consuming: a worker can be re-assigned (by an admin) to another lease and consume there, and a child already on another lease is unaffected. It does not say the consumption stops outside the metered model. Note the statement concerns the usage log, and rollback does not alter the usage log.
- **Kind:** general theorem (induction; short case analysis per step)
- **Non-vacuity:** NOT SHOWN with a Lean example of a revoked lease followed by a refused work step as a direct instance; `fresh_fork_escapes_revocation` (same file) uses a revoke in a witness, and `revoke_witness` in the refinement file shows a concrete revoked lease whose counter stays fixed. The hypotheses are easy to satisfy.
- **Read depth:** full

### `ControlStack.SC28.fork_shares_lease`  — `Scenarios/SC28Budget.lean:337`
- **Says (plain English):** In the full configuration, if the system is not halted, the parent worker holds lease `lid`, and the child worker has no assignment yet, then after a fork operation of that parent and child (any caller, any fresh-lease id argument), the child's lease is `lid`.
- **Under these hypotheses:** Not halted; parent assigned to `lid`; child not already assigned; the descendant-attribution (share) check is on. The fork operation does not check who the caller is, so any identity may trigger it in the model.
- **Does NOT say:** It does not say the child can consume (the lease may be revoked or exhausted), that every real descendant gets a fork operation recorded (a process that escapes the fork accounting is outside the model; the refinement relies on a kernel premise that a child lands in its parent's cgroup), or that a child already assigned elsewhere is moved.
- **Kind:** general theorem (essentially unfolds the fork definition; nearly definitional)
- **Non-vacuity:** `fresh_fork_exceeds_parent` and the concrete refinement fork rule show a real fork with these hypotheses; the hypotheses are easy to satisfy.
- **Read depth:** full

### `ControlStack.SC28.halt_freezes`  — `Scenarios/SC28Budget.lean:356`
- **Says (plain English):** If the system is already halted, then after any further sequence of operations (even rollbacks) the usage log is exactly as it was before.
- **Under these hypotheses:** Halted flag true in the starting state (not required to be reachable); full checks (halt check on). The halted flag can be set only by a halt operation from an admin (a model condition; admin credential secrecy is a world assumption).
- **Does NOT say:** It does not say the ledger or other state is frozen (a rollback operation still changes the ledger), that real processes are stopped, or how quickly after halt consumption ends.
- **Kind:** general theorem
- **Non-vacuity:** `no_halt_check_breaks` shows a halted run in which, with the check, nothing is recorded after halt.
- **Read depth:** full

### `ControlStack.AuthInstances.sc28_safe_authenticated`  — `Scenarios/AuthInstancesA.lean:166`
- **Says (plain English):** Operations now come as pairs (true issuer, operation). An operation that claims an identity (every operation except restart and rollback; `work w` claims worker w) is applied only if its issuer equals the claimed identity; otherwise it is dropped. For any list of such issued operations in which no operation at all is a rollback and the adversary's issuers are not admins: (i) the same three budget bounds as `sc28_safe` hold on the final state; (ii) every lease present in the final state was created by an issue operation that appears in the trace issued by an admin who is not an adversary issuer; (iii) every revoked lease was revoked by a revoke operation issued by such an admin.
- **Under these hypotheses:** World assumption: the "true issuer" recorded with each operation is the real authenticated identity (e.g. OS-reported), and the adversary's issuers (the set U) are disjoint from the admin list (credential separation). Model condition: no rollback among the operations (all operations, applied or not). Part (i) does not use the set U at all.
- **Does NOT say:** Part (i) is `sc28_safe` applied to the applied sub-trace, so authentication adds nothing to the budget bound itself: it holds for forged traces too (`forged28_consumes_without_auth` shows the harm of forging is an unauthorized grant, not a budget violation). The conclusion does not mention assignment or halt operations, so it does not state that assignments were admin-issued, though the guard also applies to them. It does not prove the platform's identity is the true issuer.
- **Kind:** general theorem (instance of a generic authenticated-log lemma; part (i) is a restatement via `authRun_eq`)
- **Non-vacuity:** `forged28_consumes_without_auth` runs the same authenticated machine on a forged trace; a nonempty honest authenticated run satisfying the hypotheses is not separately exhibited in this file, but hypotheses are easy to satisfy (U empty).
- **Read depth:** full

### `ControlStack.AuthInstances.forged28_consumes_without_auth`  — `Scenarios/AuthInstancesA.lean:187`
- **Says (plain English):** With admin 9 and global cap 1000, consider agent 1 issuing three operations: a lease issue claiming to be admin 9, an assignment claiming to be admin 9, and its own work step. If claims are never checked, the lease is created, worker 1 is assigned, and 5 units are recorded as consumed under lease 0. If claims are checked against the issuer, the forged operations are dropped and nothing is consumed.
- **Under these hypotheses:** None; a closed computation.
- **Does NOT say:** It does not show a budget bound is violated in the unauthenticated case (5 is within lease 0's budget of 100 and the cap); it shows an unauthorized grant. It is one example, not a general necessity result.
- **Kind:** negative control (shows a weakened model fails) / finite computation
- **Non-vacuity:** n/a (concrete computation).
- **Read depth:** full

### `ControlStack.SC28Liveness.honest_steps_progress`  — `Scenarios/SC28Liveness.lean:89`
- **Says (plain English):** If the system is not halted, a worker has an unrevoked lease with budget b, and the total gate charge of a list of honest work units (reported equals actual; charge is the larger of the unit and 1) fits both within the lease's remaining budget and within the remaining global cap, then running those work steps one after another accepts every one of them, and the usage log grows by exactly those entries.
- **Under these hypotheses:** Not halted, worker assigned to a lease that exists and is unrevoked, remaining lease budget at least the total charge, remaining global cap at least the total charge. No other agent acts in between (a straight sequence, no interleaving).
- **Does NOT say:** It does not say real honest jobs fit their leases or get completed (the "honest_usefulness" premise); it does not cover interleaving with other agents (that is `progress_interleaved`); it assumes the worker's charges equal what it reports.
- **Kind:** general theorem
- **Non-vacuity:** `honest_example` (same file) shows a run of three honest steps (charges 2, 3, 1) all accepted.
- **Read depth:** full

### `ControlStack.SC28Liveness.progress_interleaved`  — `Scenarios/SC28Liveness.lean:135`
- **Says (plain English):** Suppose a work step by worker w with units a would be admissible in state s (the lease exists, the charge fits the lease's remaining budget and the global remaining cap). After any sequence of other operations p, the same work step is either accepted in the new state, or one of these holds in the new state: the system is halted; the lease is revoked; the worker is no longer on that lease; the lease's spending has gone up since s; or the global spending has gone up since s.
- **Under these hypotheses:** The step is admissible at the starting state (lease/budget/cap conditions as above; one hypothesis about the worker's lease is unused, marked by an underscore). The interleaved operations are arbitrary (rollbacks allowed). Model conditions: gate charges max of actual and 1.
- **Does NOT say:** It is a weak liveness claim: the escape clause "the global spending has gone up" is triggered by any other agent's accepted work step, so in a busy system the disjunction holds trivially and guarantees nothing. It does not show honest jobs complete, nor any bound on how often an honest step is blocked.
- **Kind:** general theorem
- **Non-vacuity:** Hypotheses are satisfied by `honest_example`; no dedicated instance of the interleaved case.
- **Read depth:** full

### `ControlStack.SC28Liveness.global_cap_blocks_honest`  — `Scenarios/SC28Liveness.lean:161`
- **Says (plain English):** In a concrete run with admin 9 and global cap 10, two leases of budget 10 each, worker 1 on lease 0 and worker 2 on lease 1, worker 2 consumes all 10 units. Then worker 1's step of 1 unit is refused even though lease 0 has been entirely unspent; the usage log shows only worker 2's 10 units.
- **Under these hypotheses:** None; a closed computation.
- **Does NOT say:** It does not say this is a flaw or fix; it prices availability. It shows a shared global cap can deny honest work (denial of service by another agent), which the safety theorem does not prevent.
- **Kind:** negative control (shows a weakened model fails), in the availability sense; finite computation
- **Non-vacuity:** n/a (concrete).
- **Read depth:** full

### `ControlStack.AntiRollback.rollback_transfer`  — `Core/AntiRollback.lean:205`
- **Says (plain English):** Take any gate (a system of states, operations and effect logs) with a specification (an invariant preserved by every step, effects only appended, and logged effects acceptable in any state satisfying the invariant), and an initial state satisfying that invariant. Run any interleaving of writes, commits, restarts, and rollbacks of the store to any previously written record, with the anchor check on. Then the anchored state equals the plain run of the committed operations in order, the released effects equal that plain run's effects, the invariant holds for the plain run, every released effect is acceptable in that state, and the anchor's version equals the number of committed operations.
- **Under these hypotheses:** Model conditions (these encode world premises): there is a trusted monotonic anchor that the operator cannot reset or change except via the commit step; the operator can only restore records that were genuinely written (record integrity: it cannot forge records); the gate writes only from the anchored state and halts (fails closed) if the store is stale; effects are released only at commit; the write-then-increment protocol is respected. The gate's step and effect functions and the specification are universally quantified.
- **Does NOT say:** It does not say any operation ever gets committed after a rollback: a rollback followed by a write leaves the gate halted, so an adversary with rollback access can deny service (the claim is safety, not liveness; liveness is only for rollback-free runs in `honest_liveness`). It does not say anything about effects that occur at write time before commit (the crash window). It does not prove the anchor hardware is trustworthy.
- **Kind:** general theorem
- **Non-vacuity:** `rollback_without_anchor_double_spends` and `crash_recovery_commits` in the same file run concrete instances; the general theorem's hypotheses (a spec of the gate) are discharged for SC-28 in `sc28_rollback_safe`.
- **Read depth:** full

### `ControlStack.AntiRollback.sc28_rollback_safe`  — `Core/AntiRollback.lean:322`
- **Says (plain English):** For SC-28 with any admin list and any global cap G: after any sequence of operations that mixes legal SC-28 writes, commits, crashes/restarts and rollbacks of the stored counters to any earlier backup, the released usage log equals the usage log of the plain legal SC-28 run of exactly the committed operations, and that plain run satisfies the same three budget bounds as `sc28_safe` (total at most G; each lease within its budget; at most G work steps).
- **Under these hypotheses:** The anchor premises of `rollback_transfer` (trusted monotonic anchor, record integrity, write-then-increment protocol) as model conditions; the SC-28 operations themselves are the legal ones only (no SC-28-level rollback operation, but the storage rollback is now an adversary move). Same SC-28 model premises as `sc28_safe` (trusted meter, credential separation).
- **Does NOT say:** It bounds what is released (committed) and nothing about work done in the window between a write and its commit, when the real consumption may already have happened (effects are modelled as occurring only on release). It does not say the gate stays available under rollback (the gate fails closed and halts). It does not say the anchor is trustworthy.
- **Kind:** refinement/bridge (instance of `rollback_transfer`)
- **Non-vacuity:** `rollback_without_anchor_double_spends` gives a concrete mixed trace; hypotheses are easy to satisfy.
- **Read depth:** full

### `ControlStack.SC28Refinement.concrete_safe`  — `Scenarios/SC28Refinement.lean:539`
- **Says (plain English):** In a concrete cgroup-controller machine (a controller creates leases, launches processes into a lease's cgroup before they run, processes fork into their parent's cgroup, processes consume units that the kernel charges to the lease and to the whole run, the controller can revoke a lease (killing its processes) or halt), for any trace whatsoever (including processes launched with no placement), the kernel's counters satisfy: total accounted at most G, each lease counter at most its limit (0 if no lease), and at most G accounted consumption events.
- **Under these hypotheses:** None on the trace. Model conditions that stand in for world premises: the kernel refuses a consume that would exceed the lease limit or the run's cap (hierarchical enforcement, built into the consume rule as a refusal); a forked child is in its parent's cgroup (fork inherits); revoke and halt atomically kill the affected processes; the controller is a trusted root and counters survive for the run. The result is proved by simulating the machine in the SC-28 model and using `sc28_safe` (controller identity 0 as the only admin).
- **Does NOT say:** It does not prove the kernel enforces limits or that fork inheritance holds: these are rules written into the machine, so the theorem is a consistency check of the bookkeeping, not evidence about the kernel. The counters count only consumption by placed processes; consumption by unplaced processes is recorded separately and unconstrained (`unplaced_invisible`: 100 units consumed with G = 10 while this theorem still holds). Counters are the same list as the "usage", so the bound on actual versus charged is true by construction.
- **Kind:** refinement/bridge
- **Non-vacuity:** `placedTrace` and `revoke_witness` (same file) show nonempty runs with accounted consumption; the theorem has no hypotheses on the trace.
- **Read depth:** full

### `ControlStack.SC28Refinement.concrete_revoked_stops`  — `Scenarios/SC28Refinement.lean:553`
- **Says (plain English):** In the concrete controller machine, if a lease id is in the revoked list after some first part of a trace, then after running any second part, the kernel counter for that lease is the same as it was after the first part.
- **Under these hypotheses:** The lease id is in the revoked list after the first part. Model conditions: revoke kills all live processes in the lease's cgroup; a dead process cannot fork or consume; launching into a revoked lease is refused by the controller; a child lands in its parent's cgroup. These are rules of the machine (world premises about the kernel and the controller), not derived.
- **Does NOT say:** It does not say that the kill is instantaneous or reliable against adversarial workloads racing it (the kill is an atomic step here; the runtime measured termination within about one second on benign workloads), or that processes outside the lease's cgroup (unplaced ones) stop.
- **Kind:** refinement/bridge
- **Non-vacuity:** `revoke_witness` shows a concrete revoke after which the counter of the revoked lease stays fixed while another lease still works.
- **Read depth:** full

### `ControlStack.SC28Refinement.exclusive_placement_safe`  — `Scenarios/SC28Refinement.lean:619`
- **Says (plain English):** In the concrete controller machine, for any trace that contains no operation that launches an unplaced process (one that starts outside the run's cgroup), no consumption occurs outside the run's cgroup, and the real total (the run's accounted counter plus all unaccounted consumption) is at most G.
- **Under these hypotheses:** The trace has no unplaced launches. This is the world assumption of exclusive placement: every process that consumes descends from a controller launch with placement. In this model there is no operation that moves a process out of its cgroup, so once all launches are placed, escape is impossible by construction.
- **Does NOT say:** It does not show that real processes cannot escape their cgroup, be launched without placement, or consume off-meter by some other route (those are outside the machine's alphabet, so the model cannot even express them); it does not cover GPUs, network or other resource kinds. "Real total" means total in this model (accounted plus the model's unplaced bucket).
- **Kind:** refinement/bridge (the content is largely the exclusion hypothesis; the rest is `concrete_safe`)
- **Non-vacuity:** The placed trace in `unplaced_invisible` is a nonempty instance with a throttled real total of 10, and the hypothesis holds trivially for empty traces.
- **Read depth:** full
