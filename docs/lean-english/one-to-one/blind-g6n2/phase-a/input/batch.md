# English statements under test

### Claim 1
## `ControlStack.SC26.safe_of_sound`

- **Says (plain English):** The same safety conclusion as `sc26_safe` (every bank entry exactly approved by a non-requester approver, unique keys, total within cap) holds for any configuration of checks in which these five checks are on: payload check, requester-distinctness check, cap check, bank deduplication, bank authentication. The gate-side nonce and the halt check may be off.
- **Under these hypotheses:** `Sound C` (those five flags true), all operations legal in the same sense as `sc26_safe`. Same world assumptions.
- **Does NOT say:** That the nonce and halt check are unneeded in general: per the file's own commentary (`nonce_protects_budget_only`, not read in detail here) the nonce protects budget accounting rather than effect uniqueness and the halt check provides the halt guarantee; only the safety conclusion above does not need them.
- **Kind:** general theorem (the main inductive argument; `sc26_safe` is the special case `full`).

### Claim 2
## `ControlStack.SC26.sc26_safe_disjoint`

- **Says (plain English):** If the set of approver identities and the set of agent identities have nothing in common, then every bank entry has a request with that payload and an approval of exactly that payload by an approver who is not an agent at all (and not the requester).
- **Under these hypotheses:** Role disjointness (`every approver is not in the agents list`), a world/configuration assumption about how the launcher assigns identities; plus the legality premise of `sc26_safe`.
- **Does NOT say:** That the approver is a different human or a trustworthy one, or that the disjoint role configuration holds in the runtime (that is an assumption).
- **Kind:** definitional/trivial (a one-step corollary of `sc26_safe` and the hypothesis).

### Claim 3
## `ControlStack.SC26.sc26_once`

- **Says (plain English):** Under the deployed configuration, after any sequence of operations whatsoever, the list of reserved request ids contains no repeats: each request id is reserved, and charged against the cap, at most once.
- **Under these hypotheses:** None on the trace: no legality hypothesis, any roles and cap. The nonce check (`id` not already reserved) is what enforces it.
- **Does NOT say:** (1) That an approval is "consumed": approvals are a growing list, a single request can accumulate several approval records. The "one use" is a single reservation per request id. (2) That a business payment is made once: a new request id for the same payload can be reserved and paid separately. (3) That the bank saw the payment only once: bank-side uniqueness is `sc26_safe` (relying on receiver idempotency).
- **Kind:** general theorem (invariant on one list).

### Claim 4
## `ControlStack.SC26.halt_freezes`

- **Says (plain English):** Starting from any state whose halted flag is set, after any further legal sequence of operations, the set of messages the gate has sent to the bank is unchanged, and every entry in the bank was either already in the bank at the time of halt or was already among the sent (in-flight) messages at that time.
- **Under these hypotheses:** An arbitrary starting state with `halted = true` (not required to be reachable); all later operations legal (no gate-credential bank call); deployed checks. The halted flag is set by a halt operation from an admin identity (world assumption on authenticity).
- **Does NOT say:** (1) That no payment lands after the halt: messages already sent can still arrive and be recorded in the bank afterward (the file separately shows this can happen). The bound is "no new sends", not "nothing is paid". (2) That a halt is ever issued or processed promptly. (3) That payments reserved but not yet sent are cancelled in any further sense: they simply cannot be sent.
- **Kind:** general theorem (induction), with the freezing by construction of `step`.

### Claim 5
## `ControlStack.SC26Refinement.concrete_safe`

- **Says (plain English):** Run the concrete SC-26 machine (durable gate tables including delivery-intent rows, a volatile send-in-progress marker lost on crash, a wire of transmitted messages, an idempotent bank, acknowledgements, recover that retransmits unacknowledged intents unless halted, and halt) on any trace in which no bank call carries the gate's credential. Mapping the final concrete state to the abstract SC-26 state, the abstract safety property holds: every bank entry has a request with that payload, a reservation, and an approval of exactly that payload by a non-requester approver; keys are unique; total within the cap.
- **Under these hypotheses:** `legalC` (no direct bank call with the gate credential); recovery checks halt (the flag is fixed to `true`); the concrete bank is idempotent by key (built in). The proof is a forward simulation with an invariant (transmitted messages are logged intents; logged intents carry their request's payload). World assumption: the Python runtime implements this machine (tested, not proved); SQLite atomicity and durability, OS identity, credential separation are premises.
- **Does NOT say:** That the real gate/bank code matches the machine, that SQLite transactions are atomic and durable, or anything about liveness.
- **Kind:** refinement/bridge.

### Claim 6
## `ControlStack.SC26Refinement.concrete_halt`

- **Says (plain English):** From any concrete state that is halted, after any further sequence of legal concrete operations, the wire (the list of messages physically transmitted) is exactly as it was at the halt, and every bank entry was already in the bank or already on the wire at the halt.
- **Under these hypotheses:** Arbitrary halted starting state (not required reachable); legal operations; recovery checks halt (`true`). Mechanism: transmit and recover are refused once halted.
- **Does NOT say:** That nothing lands in the bank after the halt (messages on the wire at the halt can still be processed). It also says nothing about unsent logged intents being paid, except that they cannot be (they are not on the wire).
- **Kind:** general theorem (induction); stronger than the abstract `halt_freezes` because it speaks of transmitted messages rather than merely logged ones.

### Claim 7
## `ControlStack.SC26Authenticated.sc26_safe_authenticated`

- **Says (plain English):** Give each operation a true issuer in addition to its claimed identity; operations claiming an identity (request, approve, execute, bank call, halt) take effect only if the claim equals the issuer, deliver and arrive claim none. Take any list `U` disjoint from the approvers, and require that no bank call in the trace was issued by the gate's credential. Then (a) the SC-26 safety property `Good` holds for the final state of the authenticated run; and (b) for every bank entry, there is an identity in the approvers list, not in `U`, such that the trace contains an operation `approve a (entry id) (entry payload)` issued by that same identity `a`.
- **Under these hypotheses:** `U` disjoint from approvers; no trace element that is a bank call is issued by the gate credential (this constrains all issuers in the trace, including the adversary's). Not a hypothesis: that the adversary issues only from `U`. World assumption: the platform-reported issuer is the true issuer.
- **Does NOT say:** (1) That the adversary is confined to `U`: the trace is arbitrary, so "not in `U`" comes from `U` being disjoint from approvers; the confinement is a reading. The stronger version with an explicit adversary class is `sc26_consent_from_honest_script`. (2) That the approver was not coerced or deceived. (3) Anything about the requester's identity beyond what `Good` says.
- **Kind:** refinement/bridge (instance of the generic authenticated-issuer reduction plus an approval-provenance lemma).

### Claim 8
## `ControlStack.SC26Authenticated.forged_approval_pays_without_auth`

- **Says (plain English):** In one concrete trace, agent 1 issues everything: a request, an approve claiming to be approver 2, execute, deliver, arrive. With no identity checking, the payment lands (bank holds the entry for key 0 with payload tx1) although no approver issued anything. With the claim-checking guard, the forged approval is dropped and the bank is empty.
- **Under these hypotheses:** That one trace; roles agent 1, approver 2, admin 3, gate 9; cap 20; checked by evaluation.
- **Does NOT say:** Anything beyond that trace; it shows the guard is not vacuous, not that it is secure.
- **Kind:** negative control (finite `decide` computation).

### Claim 9
## `ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script`

- **Says (plain English):** Model the trace as an order-preserving interleaving of an honest script (the operations the trusted principals actually issue) and an adversary script all of whose operations are issued from the untrusted identity set `U`. If `U` excludes the approvers and the gate identity, and the honest script contains no direct bank call issued by the gate, then for the authenticated SC-26 run: `Good` holds, and every bank entry has an approver identity `a` such that `approve a (entry id) (entry payload)` issued by `a` is an element of the honest script.
- **Under these hypotheses:** The trace is an admissible interleaving (`AdvTrace`): the adversary script is arbitrary in length, contents and claims, but every adversary operation has its issuer in `U`; `U` has no approvers and not the gate; honest script has no gate-issued bank call. World assumption (not provable): the platform-reported identity is the true issuer, so the adversary really is confined to `U`.
- **Does NOT say:** (1) That the honest approver's act was informed or free of coercion; consent here is "the honest script contains this approve of this id and payload". (2) That the honest script cannot be manipulated into issuing it (e.g. by social engineering); the honest script is a fixed input, not adaptive. (3) Any ordering between the approval and the payment beyond what `Good` already gives.
- **Kind:** general theorem (a short corollary of `sc26_safe_authenticated` plus the interleaving lemma).

### Claim 10
## `ControlStack.SC26Liveness.honest_progress`

- **Says (plain English):** In an invariant-satisfying state that is not halted, take a request `k` that has an approval of exactly its payload by a non-requester approver and whose amount fits within the remaining cap. Then running the three honest steps in a row (execute `k`, deliver `k`, arrive `k`) leaves the entry for `k` with its request payload in the bank.
- **Under these hypotheses:** Invariant `Inv` (holds in every reachable state); not halted; request exists; `Approved`; spent plus the amount at most the cap; the "not already reserved" hypothesis is stated but not needed (the proof ignores it). The three honest steps run consecutively, with no adversary step in between, and the executing caller is arbitrary. The deployed configuration.
- **Does NOT say:** (1) Progress under interference: see `progress_interleaved`. (2) That the entry appears only once: the statement is membership only; uniqueness is `paid_once`/`sc26_safe`. (3) Any promptness or time bound, or that such an approval and cap headroom will exist; it assumes the approver approved.
- **Kind:** general theorem.
