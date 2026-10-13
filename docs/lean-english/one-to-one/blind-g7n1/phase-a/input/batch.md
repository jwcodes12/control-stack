# English statements under test

### Claim 1
## `ControlStack.AntiRollback.rollback_transfer`

- **Says (plain English):** Take any gate (a system of states, operations and effect logs) with a specification (an invariant preserved by every step, effects only appended, and logged effects acceptable in any state satisfying the invariant), and an initial state satisfying that invariant. Run any interleaving of writes, commits, restarts, and rollbacks of the store to any previously written record, with the anchor check on. Then the anchored state equals the plain run of the committed operations in order, the released effects equal that plain run's effects, the invariant holds for the plain run, every released effect is acceptable in that state, and the anchor's version equals the number of committed operations.
- **Under these hypotheses:** Model conditions (these encode world premises): there is a trusted monotonic anchor that the operator cannot reset or change except via the commit step; the operator can only restore records that were genuinely written (record integrity: it cannot forge records); the gate writes only from the anchored state and halts (fails closed) if the store is stale; effects are released only at commit; the write-then-increment protocol is respected. The gate's step and effect functions and the specification are universally quantified.
- **Does NOT say:** It does not say any operation ever gets committed after a rollback: a rollback followed by a write leaves the gate halted, so an adversary with rollback access can deny service (the claim is safety, not liveness; liveness is only for rollback-free runs in `honest_liveness`). It does not say anything about effects that occur at write time before commit (the crash window). It does not prove the anchor hardware is trustworthy.
- **Kind:** general theorem

### Claim 2
## `ControlStack.SC27Chain.sc27_safe`

- **Says (plain English):** Take any sequence of operations (writer appends, whole-log rewrites, anchoring by the independent witness, writer-published heads, verification requests, admin halts) run from the empty state with every check on. If the hash-chain head function never gives the same value to two different lists drawn from {manifests the verifier accepted} together with {logs the independent witness anchored}, then every accepted manifest is exactly equal to a log that the independent witness anchored at some earlier time.
- **Under these hypotheses:** (1) Model conditions (not world facts): the verifier's acceptance rule in `full` mode is "the manifest's chain head equals the head of some anchor entry that was recorded by the independent witness" (anchors the writer published itself are flagged and ignored; the "check current storage" and "anchored prefix plus extra suffix" shortcuts are switched off); the halt check is on. An anchoring step records the head of whatever the writer-controlled storage holds at that moment, together with a ghost copy of that list; the adversary chooses when anchoring happens. (2) A condition on the specific run: the chain head function is injective on the set of accepted manifests and independently anchored logs of the final state. This is the collision-resistance premise, stated per run, not globally; it is a world assumption for real hashes and not provable in Lean for a compressing hash.
- **Does NOT say:** It does not say the anchored log is genuine or untampered: the ghost "truth" list is not mentioned in the conclusion, and a rewrite made before anchoring is anchored and accepted. It does not say the accepted manifest is the latest anchored log: an older anchored log (truncation back to an earlier anchor) is accepted. It does not say anything about the writer's later-anchored tampered storage ("periodic anchoring launders a rewrite"; that is closed only in the extension-only model below).
- **Kind:** general theorem

### Claim 3
## `ControlStack.SC27Chain.tamper_after_anchor_detected`

- **Says (plain English):** With the concrete toy hash (the new head is 100 times the old head plus the entry plus 1, starting at 0) and one admin, two specific runs end with no manifest accepted: (i) the writer appends 5, the witness anchors, the writer rewrites storage to [7], and a manifest [7] is submitted; (ii) the writer appends 5 then 6, the witness anchors, the writer reorders storage to [6,5], and a manifest [6,5] is submitted.
- **Under these hypotheses:** None beyond the concrete toy hash and the `full` checks; it is a closed computation. No assumption about real hashes is involved.
- **Does NOT say:** It is two examples, not a statement about all tamperings. It does not show that the honest manifest ([5], or [5,6]) is accepted in those runs (that is `honest_accept`), and it does not show that detection works for a hash with collisions (`collision_breaks` shows it fails).
- **Kind:** finite computation (decide/native)

### Claim 4
## `ControlStack.SC27Chain.halt_freezes`

- **Says (plain English):** If the machine's halted flag is already set, then running any further sequence of operations (appends, rewrites, anchors, writer-published heads, verifications, further halts) leaves the entire state, including the list of accepted manifests, exactly unchanged.
- **Under these hypotheses:** Starting state is arbitrary (not required to be reachable) with the halted flag true; the halt check is on (`full`). Setting the flag is possible only through a halt operation by a caller in the environment's admin list; that is a model condition, and whether agents can obtain admin credentials is a world assumption not covered here.
- **Does NOT say:** It does not say that any trace can reach the halted state, that a real verifier process stops, or that halt happens promptly. It is a freeze of the model state only.
- **Kind:** general theorem (induction over the trace; the one-step lemma is a case split)

### Claim 5
## `ControlStack.SC27ExtensionOnly.sc27_ext_safe`

- **Says (plain English):** In the model where the witness anchors a new state only if the writer's current storage extends the witness's previously anchored state (otherwise it records a fork alarm and anchors nothing), if the chain head is injective on the accepted manifests and anchored logs of the final state, then every accepted manifest (a) is exactly some log the witness anchored, and (b) is a prefix of (or equal to) the witness's most recently anchored log.
- **Under these hypotheses:** Same per-run injectivity premise as `sc27_safe` (world assumption: collision resistance on the lists in play). Model conditions: the verifier accepts a manifest iff its chain head equals the head of some anchored log; the adversary chooses any appends, rewrites, anchoring times and manifests; there is no halt and no writer-published-head channel in this model. The witness's memory of "last anchored log" and the anchor log are outside writer control (an independence assumption built into the machine).
- **Does NOT say:** It does not say the accepted manifest is the newest anchor: any earlier anchored log (which is a prefix of the latest) is accepted, so truncation back to an earlier anchored state is NOT rejected. It does not say the anchored content is true: entries the writer appends (even fabricated) and anything it rewrites before the first anchoring get anchored on a later period. Part (b) is a direct consequence of (a) plus the anchors-form-a-prefix-chain invariant.
- **Kind:** general theorem

### Claim 6
## `ControlStack.SC27ExtensionOnly.tampered_never_anchored`

- **Says (plain English):** Start from any state that satisfies the model's invariant (anchors have correct heads, anchored logs form a prefix chain and are all prefixes of the last anchor, and every accepted manifest has a matching anchor), in which a log `l` is already anchored. Then, after running any further sequence of operations in the extension-only model, every anchor in the final state was either already there before, or is a list that extends `l`. In words: a list that does not extend an anchored log can never become anchored later.
- **Under these hypotheses:** The starting state satisfies the invariant (a model condition; every state reachable from the empty state satisfies it, as `run_inv` shows); `l` appears as the ghost copy of one anchor. No injectivity assumption is needed for this statement: it speaks about the anchored lists themselves, not heads.
- **Does NOT say:** It does not say the extending list is honest: the writer can append arbitrary entries and have them anchored. It does not say the first anchored state was genuine. It does not say no manifest of a tampered list is accepted: acceptance goes through heads, so that further needs collision resistance (it is covered by `sc27_ext_safe`).
- **Kind:** general theorem

### Claim 7
## `ControlStack.SC27ExtensionOnly.anchors_chain`

- **Says (plain English):** In the extension-only model, for any sequence of operations from the empty state, the logs anchored by the witness, in the order they were anchored, form a chain in which each is a prefix of every later one, and each anchored log is a prefix of the witness's recorded latest anchor.
- **Under these hypotheses:** None beyond the model (any appends, rewrites, anchor attempts, verifications). The extension-only check being on is part of the model, and the witness's memory and anchor log are assumed beyond the writer's reach.
- **Does NOT say:** It says nothing about whether the content is true, about what the verifier accepts (that is `sc27_ext_safe`), or about what happens if the witness's memory can be overwritten.
- **Kind:** general theorem (read off an inductive invariant)

### Claim 8
## `ControlStack.SC27ExtensionOnly.alarm_iff`

- **Says (plain English):** For any state, one anchoring attempt by the extension-only witness appends the current storage to the alarm list exactly when the current storage does not extend the last anchored state (a first anchoring, with no previous anchor, never alarms); and when it does not extend, the list of anchors is left unchanged.
- **Under these hypotheses:** Only the model definition of the witness step; no assumption about hashes (the model compares actual lists, not heads).
- **Does NOT say:** It does not say anyone reads or acts on alarms. It does not describe the real Python witness: the real witness compares heads, and the refinement file records that it is silent on truncation to empty (`empty_truncation_silent`), where this abstract model would alarm. It says nothing about alarms being tamper-proof.
- **Kind:** general theorem (case analysis on one step; close to a restatement of the witness step's definition)

### Claim 9
## `ControlStack.SC27Refinement.concrete_ext_safe`

- **Says (plain English):** In a more concrete machine that mirrors the runtime's events (writer appends, rewrites and self-published heads; witness examines storage, remembering only the length and head of its last anchor; verifier recomputes a manifest's head and accepts iff it matches a witness-recorded anchor head, not a writer-published head), every accepted manifest is a list that the witness anchored, and a prefix of the witness's latest anchor. This transfers `sc27_ext_safe` to that machine by a forward simulation.
- **Under these hypotheses:** Two world-type assumptions: (1) at every witness examine step, the chain head is injective on the pair (last anchored list, the same-length prefix of current storage) (`TraceInj`, collision resistance for the head comparison); (2) the chain head is injective on the accepted manifests and the anchored lists of the final state. Model conditions: the deployed verifier (`trustWriter = false`); the writer cannot modify the witness's memory or log; the verifier reads only the witness's log; fsync durability of the witness's log. The anchored lists in the conclusion are ghost copies kept by the model; the real witness stores heads and lengths.
- **Does NOT say:** It does not prove that the Python harness implements this machine (only tested, run-1). It does not rule out the recorded gap that the witness stays silent on truncation to empty (it only says nothing wrong is accepted). The "latest anchor" conclusion is only a prefix statement: an older anchored list is still accepted. It is not a statement about real SHA-256 beyond the two injectivity hypotheses.
- **Kind:** refinement/bridge

### Claim 10
## `ControlStack.SC27Refinement.concrete_tampered_never_anchored`

- **Says (plain English):** In the concrete machine, split any trace into a first part and a second part. If a list `l` is among the witness's anchor records after the first part, then every anchor record in the log after both parts is either one that was already there after the first part, or is a list that extends `l`. So nothing that fails to extend an anchored list is anchored afterwards.
- **Under these hypotheses:** The injectivity condition at every examine step across the whole combined trace (`TraceInj`, collision resistance on the head comparison); deployed verifier setting; witness independence as above. No injectivity assumption on accepted lists is required here, only on the witness's own head comparisons.
- **Does NOT say:** It does not say what extends `l` is honest; it does not cover truncation to empty being alarmed (the witness is silent there, though nothing is anchored); it does not cover a rewrite before the first anchoring.
- **Kind:** refinement/bridge
