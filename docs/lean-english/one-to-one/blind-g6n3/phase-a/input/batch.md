# English statements under test

### Claim 1
## `ControlStack.SC26Liveness.progress_interleaved`

- **Says (plain English):** In an invariant state, take a request `k` that has an exact, independent approval. Insert arbitrary legal adversary operation lists before, between and after the three honest steps (execute `k`, deliver `k`, arrive `k`). Then at the end one of three things is true: the gate is halted; or the payment for `k` with its request payload is in the bank; or, at the moment just before the honest execute, `k` was not yet reserved and the cap was already exhausted for it (spent plus amount exceeds the cap).
- **Under these hypotheses:** `Inv` on the start; request and `Approved` at the start; all adversary operations legal (no gate-credential bank call). Halt is among the legal adversary operations (a `halt` carrying an admin's identity), so the first disjunct can be forced by any operation carrying an admin identity.
- **Does NOT say:** (1) That honest operations succeed against an adversary able to halt or to exhaust the cap: those are the exits, and in the model any `halt` with an admin identity is allowed. (2) A bound on time or on how often the exits occur. (3) That the payment is made exactly once (that is `sc26_safe`).
- **Kind:** general theorem.

### Claim 2
## `ControlStack.SC26Liveness.Concrete.crash_tolerant_progress`

- **Says (plain English):** From a reachable concrete state with a delivery-intent row for key `k`, take any legal trace of the form `pre`, then `recover`, then `mid`, then `bankProcess k`, then `post`, with any crashes anywhere, in which the gate is not halted when `recover` runs. Then at the end key `k` is in the bank's ledger, exactly once.
- **Under these hypotheses:** Reachable concrete state `runC ... ops0` with legal `ops0`; a delivery row with id `k` exists; all later operations legal; not halted just before `recover`; the trace contains a `recover` followed later by a `bankProcess k`. That last structure is the "fairness premise": it is an assumption about the schedule, not something the gate guarantees. The conclusion is about the key only: payload equality is not stated in this item.
- **Does NOT say:** (1) That a recover and a bank processing ever happen: `crashes_forever_no_progress` shows that without them the intent is never paid. (2) That the gate is not halted at later steps or that the network is reliable: the concrete wire here never loses messages; losing messages is the lossy files. (3) That the payment was authorized: authorization comes from `concrete_safe`.
- **Kind:** general theorem; the fairness premise makes the conclusion close to "if the bank processes a transmitted copy, the key lands".

### Claim 3
## `ControlStack.SC26LossyLiveness.lossy_safe`

- **Says (plain English):** Extend the concrete machine with three adversary-controlled network operations (drop an in-flight message, duplicate one, have the bank process the j-th in-flight message in any order). For any trace of these (including all the concrete operations) in which no bank call carries the gate credential, the abstract SC-26 safety property holds for the final state: every bank entry exactly approved by a non-requester approver, keys unique, total within cap.
- **Under these hypotheses:** Legal lossy trace (network operations unrestricted, gate-credential bank calls excluded); the bank's processing is idempotent by key (`dedup = true` is fixed in the statement, so receiver idempotency is a built-in premise); recovery checks halt. Forward simulation maps drop and duplicate to no abstract steps.
- **Does NOT say:** That the bank is idempotent (that is baked in; `no_dedup_lossy_pays_twice` shows a non-idempotent bank pays twice), or anything about liveness under loss.
- **Kind:** refinement/bridge.

### Claim 4
## `ControlStack.SC26LossyLiveness.lossy_rounds`

- **Says (plain English):** From a reachable lossy state with a delivery-intent row for key `k`, take a window of retransmission rounds, each a list of operations, then the gate's `recover`, then a list of operations. Suppose at least one round in the window is a "delivering" round: the operations after its `recover` consist of a drop-free segment followed by `bankProcess k`. Suppose also the gate is not halted at the end of the window. Then key `k` is in the bank at the end of the window, and after any legal continuation `k` appears exactly once among the bank keys.
- **Under these hypotheses:** Legal operations everywhere; the existence of one delivering round in the window (the "fairness" premise), stated as a property of the trace itself; the gate not halted at the end of the window; the delivery row for `k` existing from the prefix. The "at most R consecutive losses" bound is not a formal hypothesis: the premise is simply that some round in the given list delivers, and the "R" is the length of the list.
- **Does NOT say:** (1) That bounded loss holds of any real network: the premise says one of the rounds has a drop-free segment before `bankProcess k`, i.e. it is essentially the hypothesis of `lossy_progress` restated per round, so the conclusion is close to the premise. (2) Anything if the network drops every retransmission (`drop_all_no_progress` shows no progress then). (3) That the gate is not halted: this is a hypothesis.
- **Kind:** general theorem; the conclusion follows quickly from `lossy_progress` by splitting the trace at the delivering round (near-restatement of its premise plus the exactly-once from safety).

### Claim 5
## `ControlStack.SC26LossyHalt.lossy_halt_keys`

- **Says (plain English):** From any lossy machine state that is halted, after any legal sequence of lossy operations (drops, duplicates, reorderings, crashes, recover/transmit attempts, direct bank calls), every key in the bank's ledger was already a key in the ledger at the halt or a key of a message in flight at the halt.
- **Under these hypotheses:** An arbitrary halted starting state (not required reachable); legal operations; bank processing idempotent (fixed `dedup = true`); recover checks halt (`true`).
- **Does NOT say:** That no key lands after the halt: keys of messages in flight at the halt may still land, in any order, after the halt; "no new key" means no key that was not in the ledger or in flight at the halt. It also does not say a halt is ever issued, and it holds only for the deployed (halt-respecting) recovery (`recover_ignores_halt_lossy` shows the older design fails).
- **Kind:** general theorem (induction).

### Claim 6
## `ControlStack.SC26LossyHalt.tagged_rounds`

- **Says (plain English):** Run the lossy machine while tagging each physically transmitted copy with a fresh id (a duplicate keeps its copy's id; a drop removes one tagged copy). From a reachable state, take a window of retransmission rounds. Suppose that in some round the retransmission by `recover` includes a copy of key `k` and that copy's id is later processed by the bank (an in-flight copy at an index holding that id is delivered), drops of other copies being allowed anywhere. Then key `k` is in the bank at the end of the window and, after any legal continuation, appears exactly once among the bank keys.
- **Under these hypotheses:** Legal operations; the existence of one round whose tagged copy of `k` is delivered before all copies of it are dropped, stated as a property of the trace (`DeliversT`). The existence of the copy of `k` in the recover batch itself implies the gate was not halted and `k` had an unacknowledged intent at that point; no separate "not halted" hypothesis. This is the "per-copy fairness" premise, strictly weaker than the all-or-nothing `Delivers` premise by `per_copy_weaker`.
- **Does NOT say:** (1) That such a delivery ever occurs on a real network; the premise is on the trace. (2) That the gate retransmits: `recover_batch_has_k` (not part of this item) shows the gate does when not halted; but a window with no recover has nothing to say. (3) That the payment was authorized or the payload right (the conclusion is about the key; authorization comes from `lossy_safe`, which the proof invokes for exactly-once).
- **Kind:** general theorem; conclusion follows from the per-round premise (the delivered copy of `k` is processed, which already lands the key) plus safety for uniqueness.
