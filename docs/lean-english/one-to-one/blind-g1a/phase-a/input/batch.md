# English statements under test

### Claim 1
## `ControlStack.EgressGate.step_safe`

- **Says (plain English):** For any fixed policy `p` (a list of rules, each pairing an authority string with a pinned peer address/port/protocol), any state `s`, and any single action `a`: if the state satisfies the invariant, so does the state after the action. The invariant says two things: (i) if the sandbox is marked active then its topology flags are all true ("safe": no external route, no inherited authority, private namespaces, protected policy, no host deputy); (ii) every recorded outbound socket attempt (including failed connects) originated from the gateway and targets a peer that appears in the policy's pinned peers. The actions are: launch with a topology, start the gateway with a supplied policy (it is up only if the supplied policy equals `p`), request via an authority (the gateway looks the authority up in `p` and, if found and the gateway is up and the sandbox is active, records an attempt to the pinned peer), a direct socket attempt by the sandbox, tamper-with-policy, and crash-gateway.
- **Under these hypotheses:** The state satisfies the invariant. In the model: `launch t` sets `active` to whether `t` is safe; `directAttempt` has an effect only when active and the topology is not safe (and the invariant rules that combination out); `tamperPolicy` is a no-op (the policy `p` is a fixed parameter; this IS the assumption `policy_integrity`, built into the model rather than proved); `crashGateway` only turns the gateway off.
- **Does NOT say:** (a) Not that a real sandbox cannot open sockets: the "safe" flags are inputs to `launch`; Lean has no connection between the flags and Linux namespaces, routing, inherited file descriptors, or host helper processes. (b) Not that peers listed in the policy are themselves harmless, nor anything about what flows through a pinned tunnel (the file header excludes CONNECT tunnel bytes). (c) Does not show that any particular state satisfies the invariant: reachability from a real start state needs the start state to satisfy it (an inactive state with no attempts does, but no named instance is given).
- **Kind:** general theorem (inductive preservation; the proof is case analysis on the model's own guards and the lemma `lookup_pinned`)

### Claim 2
## `ControlStack.EgressGate.trace_safe`

- **Says (plain English):** For any policy, any state satisfying the invariant, and any finite list of actions, running the actions in order from that state ends in a state that also satisfies the invariant. So: every outbound attempt ever recorded has the gateway as origin and a pinned peer as target, and an active sandbox always has a safe topology flag set.
- **Under these hypotheses:** the same invariant on the starting state; arbitrary action list (every action type, including repeated launches, policy tampering, gateway crashes). Same model assumptions as `step_safe`.
- **Does NOT say:** (a) Not "the sandbox cannot connect anywhere unauthorised" in the real world, only in the model whose `directAttempt` is defined to be inert when the flags say safe. (b) Not about states reachable from a specific real initial state unless that initial state satisfies the invariant. (c) The word "unauthorised" is modelled as "origin other than the gateway, or a peer not in the policy"; peers reachable through gateway-originated attempts are authorised by definition, even though the sandbox picks the authority key.
- **Kind:** general theorem (induction over `step_safe`; the invariant holds essentially by the construction of the model)

### Claim 3
## `ControlStack.SC05.cap_does_not_prevent`

- **Says (plain English):** There exist a sender strategy (for a secret bit, emit a specific one of 65536 possible outputs) and a receiver decoder (read the output and report a bit) such that, for the identity observation of the outputs, the receiver recovers the bit with probability exactly 1. So a limit of 16 bits (65536 distinguishable outputs) per message does not prevent two colluding parties agreeing on a binary choice with certainty.
- **Under these hypotheses:** None beyond the model: the sender is free to emit any of the 65536 outputs, the receiver sees the output exactly, and the secret is a uniformly chosen bit (no shared seed is even needed here).
- **Does NOT say:** (a) Not that any real agents can or do coordinate; it shows only that in the model with a freely choosable, receiver-distinguishable output, a bit passes. (b) Not about the malicious action: coordination is modelled as agreement on a secret bit; no action is executed. (c) It is not a defence claim at all: it is a no-go showing a size cap is not the right control.
- **Kind:** witness / non-vacuity example (existential witness; it instantiates `one_bit_coordinates` at `view = id`, outputs 0 and 1)

### Claim 4
## `ControlStack.SC05.zero_dependence_is_blind`

- **Says (plain English):** If the distribution of the mediated output (given the shared seed) does not depend on the secret at all, then for every seed distribution and every decoder, the probability of recovering a uniform secret equals exactly 1/|M| (the blind guess rate).
- **Under these hypotheses:** the seed distribution, the output distribution (per seed) and the decoder rows are probability distributions; the output law is a function of the seed only (the secret is not an argument), so "zero secret-dependence" is built into the type of the encoder rather than assumed separately. Whether a real output has zero secret-dependence is world assumption `zero_dependence_measured` (NOT_PROVED).
- **Does NOT say:** (a) Not that real outputs are independent of the secret; the theorem takes this as the shape of the encoder. (b) Not about coordination on a bit: it applies to a uniformly random secret, and if the secret is not uniform the blind rate changes. (c) The conclusion is an equality only for this blind encoder; it does not bound a dependent one.
- **Kind:** general theorem (elementary; the hypothesis that the encoder ignores the secret does most of the work)

### Claim 5
## `ControlStack.SC05.forbidden_never_executes`

- **Says (plain English):** Consider a system whose only operation is "request action a" and whose state is the list of executed actions; the gate refuses any request whose action id is in the `forbidden` list and otherwise appends it. Then, starting from nothing executed, after any sequence of requests no executed action is in the `forbidden` list.
- **Under these hypotheses:** `forbidden` is any list of natural-number action ids and the request sequence is arbitrary (so any signal the colluders use can only influence which ids are requested). The gate is always on in this system (`step forbidden true`). That the real prohibited action can only run through this gate, that actions are correctly identified by id, and that no alias for the same harm exists, are world assumptions (`action_gate_complete`, NOT_PROVED; semantic scope in the file header).
- **Does NOT say:** (a) Not that the real system has no other route to the action, or that "malicious action" is exactly the `forbidden` set: the list is an input chosen outside the model. (b) Not that colluding agents are prevented from coordinating or achieving the same harm via a non-forbidden action. (c) Because the model has exactly one operation and the gate is a filter on it, the property holds by construction; the file also gives `forbidden_executes_without_gate` showing the filter is doing the work.
- **Kind:** general theorem (inductive, by construction of the gate)

### Claim 6
## `ControlStack.SC06.sc06_safe`

- **Says (plain English):** Fix any policy (lists of user ids, admin ids and sensitive tool ids). Run any finite sequence of operations (typed writes, raw writes, reads, user confirmations, actions, halts) from the empty initial state, with the "full" check set (canonicalisation on, single write path, provenance check on, halt check on). Then in the final state (a) no entry in any agent's context is marked as free text, and (b) every executed action whose tool is sensitive and which is labelled "value came from another agent's artifact" has a confirmation record in the final state with the same agent, tool and value, with a confirmation id the action cites, and with a confirming id that is in the policy's users list.
- **Under these hypotheses:** None on the operation sequence (it is fully arbitrary: any caller ids, any ids, any values). The model assumptions that make it true: the typed write path stores no free text (canonicalisation drops it), raw writes are refused, reads produce a context entry whose "from another agent" flag is `writer != reader` where writer is the caller id given to the write operation, and an action reads its "from other" flag from the first context entry of that agent with that value.
- **Does NOT say:** (a) "Confirmed by a user" means only that a `confirm` operation was processed whose caller id is in the users list. Since the operation sequence is arbitrary, nothing in Lean stops the attacking agent's trace from containing a confirm with a user's id, or a write using the victim's id as caller (so the artifact is labelled as the victim's own); this is exactly the unmodelled credential separation. (b) "Typed" fields are arbitrary natural numbers, so the theorem excludes only the model's separate free-text field, not the carrying of an instruction in a typed value (the file notes this is the SC-05 covert channel). (c) The "from another agent" label is attached to the first context entry matching (agent, value); if the same value also entered the reader's context from its own artifact earlier, the action is labelled not-from-other and needs no confirmation, so "a value from another agent's artifact" is true only relative to those labels. Also a confirmation is not consumed: the same confirmation can authorise repeated actions on the same (agent, tool, value).
- **Kind:** general theorem (inductive invariant over the model; true largely by construction of the checks)

### Claim 7
## `ControlStack.SC06.halt_freezes`

- **Says (plain English):** With the full check set, if the state is already halted, then running any sequence of operations leaves the state exactly unchanged (no write, read, confirmation or action has any effect, and a second halt changes nothing).
- **Under these hypotheses:** The starting state is marked halted; that is all (the state need not be reachable from the initial one). The halted flag is set only by a `halt` operation whose caller id is in the admins list; that the real halt is performed only by an admin is a credential assumption not modelled.
- **Does NOT say:** (a) Not that halting happens: it says nothing about when or whether a halt is issued. (b) Not that real in-flight actions stop; the model's halt is atomic. (c) Not that agents cannot impersonate an admin to cause a halt (that would be a denial of service rather than a leak, but is also unmodelled).
- **Kind:** general theorem (by construction: every operation is a no-op once halted)

### Claim 8
## `ControlStack.SC07Liveness.sc07_safe`

- **Says (plain English):** In a model gateway with an allowlist of destinations, a per-window quota q, tick operations that open new windows, and an admin halt, run any sequence of sends (to any destination, of any size), ticks and halts from the initial state with all three checks on. Then every forwarded send went to an allowlisted destination, and for every window the total bits forwarded in that window is at most q. (A send that would push the window over q is dropped whole.)
- **Under these hypotheses:** None on the operation sequence. In the model, "bits" is only the size field `n` of each send; a send of zero bits to an allowlisted destination is forwarded and consumes no quota.
- **Does NOT say:** (a) The total over the whole run is not bounded by q: ticks open new windows and are ordinary adversary-chosen operations in the model (the later theorem `total_le` bounds the total by q times the number of windows opened). So "never sends more than its byte quota" holds per window only. (b) The quota counts payload size only; the destination chosen among allowlisted ones, the number and order of (possibly zero-size) sends, and timing carry information the model does not count (these are `adversarial_channels`). (c) Nothing about halt here: halting is a separate theorem.
- **Kind:** general theorem

### Claim 9
## `ControlStack.SC07Refinement.concrete_safe`

- **Says (plain English):** In a concrete model of the gateway's forward chain (allowlisted (ip, port) pairs, a quota object with a kernel-style `consumed` counter that adds each packet's on-wire length and then drops the packet if `consumed` has reached the quota threshold Q, and a halt that replaces the chain with a drop rule): for any sequence of packets (to any address and port, any payload and header sizes), quota resets and halts, starting from the initial state and with the quota rule present, every forwarded packet went to an allowlisted (ip, port), and for every window the total forwarded payload bytes is at most Q - 1.
- **Under these hypotheses:** the quota rule is present in the configuration (`quotaRule = true`); no restriction on the packet/reset/halt sequence. The model's trusted-kernel semantics (exact installed rules, `consumed` accounting, crossing packet dropped, header bytes counted) are the assumption `model_runtime_correspondence`, tested only on one host.
- **Does NOT say:** (a) The bound is per window, and `resetQuota` is an operation in the arbitrary sequence; in the runtime the quota is per run (one window), but the Lean statement does not bound the total across resets. (b) Not that the Python gateway installs this ruleset or that the kernel behaves as modelled (tested, not proved). (c) Not about return traffic, retransmission, or covert channels; payload bytes only, and with Q = 0 the natural subtraction gives 0 and every packet is dropped.
- **Kind:** refinement/bridge (transfers `SC07Liveness.sc07_safe` through a forward simulation)
