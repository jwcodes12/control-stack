# Plain-English statements, part G0

Source files (paths relative to `/var/tmp/sol-deployment-slice-20261010`): `ControlStack/Deployment/Contracts.lean`, `ControlStack/Deployment/R2Contracts.lean`, `ControlStack/TrustedBroker.lean`, `ControlStack/Deployment/TranscriptReplay.lean`. Supporting definitions read: `ControlStack/Scenarios/SC26Transaction.lean`, `ControlStack/Core/Gate.lean`, `ControlStack/Core/CheckedTrace.lean` (the `verified`/`recordedEnd` definitions), `ControlStack/Deployment/Witnesses.lean`.

## Scenario DEPLOY: Deployment verifier: accepted configuration + broker protocol model + transcript replay

**Harm (one sentence).** An agent causes a file to appear in the protected sink that is not attributable to a reviewed, exactly approved, once-consumed release within a shared budget, or an agent/deputy has an authority path to the sink or database that avoids the broker/receiver.

**Adversary and scope (from the scenario).** Two untrusted agent UIDs in containers sharing one budget; trusted broker, receiver, reviewer and approver; the configuration is read from Compose plus a daemon inventory. The Lean side covers a finite configuration graph (the IR) and a transition model of the SQLite broker. It does not cover the Python code, Docker or the kernel. Status in the scenario: CONDITIONAL.

**What the Lean claims, taken together, and what they leave to assumptions.** There are three separable layers. (1) If a hand-built finite graph (`IR`) passes the `Accepted` checks, then no chain of edges in that graph lets an agent node reach the sink or database without passing through the broker or receiver. The sink and database authority edges all originate at the receiver or broker, and no agent shares the receiver's UID. (2) Two abstract protocol models, an SC26 "gate and bank" model and the `TrustedBroker` SQLite-transaction model, satisfy budget, key-uniqueness and one-use invariants over every finite sequence of model steps. (3) A single recorded 10-step transcript is replayed as a chain of model steps, and one of its replayed denials is shown to be a genuine model denial. The theorems that join these layers to the real sink (`deployment_safe`, `deployment_broker_safe`) take the graph being complete (`ExtractionFaithful`) and the real sink publications matching the model (`ProtocolRefinement` / `BrokerProtocolRefinement`) as hypotheses. The "published sink nonces are a sublist of consumed nonces" and "caller uid is an agent node's uid" facts are inputs, not outputs. The conclusions say a used approval exists for each published nonce. They do not say who signed it, that it matched the file's digest, or that the artifact was reviewed. Those facts are in the broker model's release guard but are not surfaced in the final theorem statements. World assumptions from the scenario, all `NOT_PROVED`: **faithful_extraction** (the IR contains every authority edge the real deployment has); **protocol_refinement** (the Python broker and receiver implement the Lean transition model, and sink files correspond to published nonces); **tcb** (kernel, Docker daemon reports, SQLite, Python, scanner and serializer are trusted).

---

### `ControlStack.Deployment.Accepted`  — `ControlStack/Deployment/Contracts.lean:99`
- **Says (plain English):** This is a definition, not a theorem. A deployment description `d` (a list of nodes, a list of edges, and the identities of the receiver, broker, sink and database) is "accepted" when six groups of finite checks all pass.
  1. *Basic.* Every edge is a known edge. Every edge marked "authority" that targets the sink comes from the receiver. Every authority edge that targets the database comes from the receiver or the broker. No node is privileged or on the host network. No agent node has the receiver's UID. The receiver has an authority edge to the sink. Every UID is positive, i.e. nobody is root.
  2. *Roles.* There are exactly six nodes: two agents, one broker, one receiver, one reviewer and one approver. A node is an agent exactly when its role number is 0. It is the broker exactly when its id is the broker id and its role is 1, and likewise for the receiver and role 2.
  3. *Identities.* Two distinct nodes share a UID only if they are the broker and the receiver. Every other UID is unique.
  4. *Runtime.* Every node's `runtimeMatch` flag is true.
  5. *Writers.* Every edge, authority-marked or not, that targets the sink goes from the receiver and is a write edge. The set of write edges into the sink has exactly the receiver as its source list. Every edge into the database comes from the broker or receiver. There are exactly two write edges into the database, one from the broker and one from the receiver.
  6. *No-bypass.* For every agent node `a`: the set `reachable d a.id` (computed by following every edge except edges that land on the broker or receiver) does not contain the sink or the database. That set is also closed under such edges.
- **Under these hypotheses:** None; it is a predicate on a finite structure. The inputs it reads (`authority`, `unknown`, `write` flags on edges; `agent`, `privileged`, `hostNetwork`, `role`, `runtimeMatch` flags and UIDs on nodes) are produced by an extractor from Compose and the daemon inventory. That the extractor tells the truth is a **world assumption** (`faithful_extraction`, `tcb`). The `runtimeMatch` flags are, in the source's own words, "input observations, not independent attestation".
- **Does NOT say:** (a) Nothing about the Python code, the kernel, or what the broker or receiver actually do. Edges that land on the broker or receiver are treated as mediated and are not examined further. (b) It does not say the configuration is complete: an authority path through an edge the extractor did not list is invisible. (c) It fixes the topology to exactly six nodes (two agents), so it is not a general checker for other deployments.
- **Kind:** `definitional/trivial` (a definition; its decidability instance is by `infer_instance`).
- **Non-vacuity:** `Deployment.clean_accepted` (`Contracts.lean:242`, by `decide`) shows the concrete `clean` IR is accepted. `writable_mount_refutes`, `unknown_refutes`, `Witnesses.uid_collision_refutes` and `Witnesses.database_bypass_refutes` show that adding a writable-mount edge, an unknown edge, a UID collision or a database edge makes it fail.
- **Read depth:** `full`

### `ControlStack.Deployment.exclusive_sink`  — `ControlStack/Deployment/Contracts.lean:114`
- **Says (plain English):** For an accepted deployment, any edge in the IR that is marked as an authority edge and whose target is the sink has the receiver as its source. So, as far as the IR lists, only the receiver holds authority over the sink.
- **Under these hypotheses:** `Accepted d`, and the edge is a member of `d.edges` with `authority = true` and `target = d.sink`. These are conditions on the model. The proof reads off the second clause of `BaseAccepted`.
- **Does NOT say:** (a) It does not say that no real process other than the receiver can write to the real sink. That needs the IR to contain all real authority edges (an unproved assumption, `faithful_extraction`). (b) It covers only edges flagged `authority = true`. The stronger "every edge, flagged or not, into the sink comes from the receiver" fact lives in the writers check but is not what this theorem states. (c) It says nothing about what the receiver writes.
- **Kind:** `definitional/trivial` (a projection of a field of `Accepted`).
- **Non-vacuity:** `Witnesses.sink_positive` applies it to `clean` with the edge from node 3 to the sink.
- **Read depth:** `full`

### `ControlStack.Deployment.database_custody`  — `ControlStack/Deployment/Contracts.lean:118`
- **Says (plain English):** For an accepted deployment, any authority edge in the IR that targets the database has the receiver or the broker as its source.
- **Under these hypotheses:** `Accepted d`, plus the edge being in `d.edges`, marked authority, targeting `d.database`. Conditions on the model.
- **Does NOT say:** (a) The database is not protected against the broker or receiver themselves. (b) It does not say real agents have no real path to the database; it holds only relative to the IR. (c) It says nothing about which of the two (broker or receiver) wrote what.
- **Kind:** `definitional/trivial` (a projection of the third clause of `BaseAccepted`).
- **Non-vacuity:** `Witnesses.database_positive` (edges 2 to 5 in `clean`).
- **Read depth:** `full`

### `ControlStack.Deployment.runtime_exclusive`  — `ControlStack/Deployment/Contracts.lean:128`
- **Says (plain English):** If the configuration is accepted, and every edge in a list `actual` of real, observed authority edges is also in the IR, then every real authority edge into the sink comes from the receiver.
- **Under these hypotheses:** `Accepted d`, and `Faithful d actual`. The latter is a structure with one field: every edge in `actual` is a member of `d.edges`. This second hypothesis is a **world assumption** (that observed runtime edges are included in the extraction). The source describes it as "the residual implementation/environment premise, not kernel-proved". The edge `e` in question must be in `actual` and be marked `authority = true` with target the sink.
- **Does NOT say:** (a) It does not show that `actual` is the complete list of real edges. Faithfulness is only "everything in `actual` is in the IR", and `actual` is whatever the caller supplies. (b) The name "runtime" is about the premise, not about monitoring anything at runtime. (c) It adds nothing to `exclusive_sink` beyond composing it with the inclusion hypothesis.
- **Kind:** `definitional/trivial` (`exclusive_sink` applied to a member of `d.edges`).
- **Non-vacuity:** `Witnesses.runtime_positive` with `Witnesses.extracted : ExtractionFaithful clean receiverNode clean.edges`. That takes `actual` to be the IR's own edges, so it shows consistency only. `Witnesses.omitted_writer_refutes` shows an unlisted writer edge is not "faithful".
- **Read depth:** `full`

### `ControlStack.Deployment.agent_not_receiver_uid`  — `ControlStack/Deployment/Contracts.lean:134`
- **Says (plain English):** If the configuration is accepted, then no node flagged as an agent has the same UID as the node that is the receiver. So an agent cannot carry the receiver's operating-system identity.
- **Under these hypotheses:** `Accepted d`; `r` is a node in the IR with id equal to the receiver id; `a` is a node in the IR with `agent = true`. Conditions on the model. That the Compose-reported UIDs are the real process UIDs is the **world assumption** (`tcb`, `faithful_extraction`).
- **Does NOT say:** (a) It does not say an agent cannot act as the receiver by other means (stolen credentials, shared files, ptrace, etc.). Only the UID field is compared. (b) It does not say the broker is separate from the receiver. In `clean` and in the `Accepted` identity check, the broker and receiver deliberately share one UID. (c) It does not say agents are distinct from each other.
- **Kind:** `definitional/trivial` (a projection of the fifth clause of `BaseAccepted`).
- **Non-vacuity:** `Witnesses.identity_positive` (`agentA.uid = 23701`, receiver uid `23700`).
- **Read depth:** `full`

### `ControlStack.Deployment.agent_call_legal`  — `ControlStack/Deployment/Contracts.lean:143`
- **Says (plain English):** For an accepted deployment, a direct call to the external system (the "bank"/sink service) made under an agent node's UID is a "legal" operation of the SC26 model. In that model "legal" means the caller does not carry the gate's own credential. The role record is built so that the gate credential equals the receiver node's UID.
- **Under these hypotheses:** `Accepted d`; `r` is the receiver node and `a` an agent node in `d.nodes`. `approvers` and `admins` are arbitrary lists: the roles function only fills the agent-UID list from the IR, and nothing is required of the approver or admin lists (they may overlap agent UIDs). The identification "SC26 gate credential = receiver's UID" is part of how `roles` is defined and is a modelling choice that must be borne out in the real system. The comment in the source says role IDs and actual SO_PEERCRED bindings are residual.
- **Does NOT say:** (a) It does not say the agent cannot call the bank or the sink; it says that in the model the call carries a non-gate credential, and the model's bank rejects such calls. That rejection is built into the SC26 step function. (b) It does not say anything about approver or admin credential separation. (c) It does not establish that the real sink service authenticates by UID.
- **Kind:** `definitional/trivial` (it is `agent_not_receiver_uid` re-read through the definitions of `legal` and `roles`).
- **Non-vacuity:** `Witnesses.legal_call_positive`.
- **Read depth:** `full`

### `ControlStack.Deployment.protocol_safe`  — `ControlStack/Deployment/Contracts.lean:151`
- **Says (plain English):** In the SC26 gate-and-bank model, start from the empty state and run any finite sequence of operations (requests, approvals, executions, delivery retries, message arrivals, direct bank calls, halts), as long as no direct bank call carries the gate's credential. Then in the final state: (1) every entry in the bank has a stored request with exactly that payload, the request id has been reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester; (2) bank keys are all distinct; (3) the sum of the bank entries' amounts is at most the cap.
- **Under these hypotheses:** Every operation in the list is `legal` (the only restriction is that a `bankCall` is not made with the gate's credential; all other operations are unrestricted). The model's checks are all enabled (`SC26.full`): approval distinctness, payload-exact approval, nonce guard, cap guard, halt check, bank deduplication, bank authentication. The roles record `R` (agents, approvers, admins, gate credential) and `cap` are arbitrary.
- **Does NOT say:** (a) There is no review step in SC26. "Approved" means an entry in the approvers list that differs from the requester; it does not include any independent reviewer of the artifact. (b) Nothing assures that the approvers are not also agents: that requires a separate disjointness hypothesis (`sc26_safe_disjoint`), not used here. An `approve` carrying an approver identity is treated as that approver's genuine act. (c) Exactly-once is per request id, not per business intent: the same payload requested twice can be paid twice. (d) It is a statement about the abstract model, not the Python.
- **Kind:** `general theorem` (a one-line wrapper of `SC26.sc26_safe`, whose proof is an induction over operation lists using the invariant `SC26.Inv`).
- **Non-vacuity:** `Witnesses.protocol_positive` and `Contracts.useful_acceptance` (a concrete trace pays exactly once). `SC26.honest_trace_pays` also shows the honest path pays.
- **Read depth:** `full`

### `ControlStack.Deployment.one_use`  — `ControlStack/Deployment/Contracts.lean:155`
- **Says (plain English):** In the SC26 model with all checks on, after any finite sequence of operations at all (no legality premise), the list of reserved request ids contains no repeats. So each request id is reserved, and its amount is charged against the cap, at most once.
- **Under these hypotheses:** None beyond the model definition (the `execute` step refuses to reserve an id already in the reserved list when the nonce check is on, which it is in `full`). It holds for arbitrary roles, cap and operation list.
- **Does NOT say:** (a) It does not say the same payment cannot happen twice under two different request ids (separate requests with identical content are independent). (b) It concerns reservation inside the gate, not what reaches the sink. (c) It is about SC26's request ids, not about the broker model's nonces.
- **Kind:** `general theorem` (wrapper of `SC26.sc26_once`, an induction).
- **Non-vacuity:** `Witnesses.one_use_positive`; `Contracts.nonce_disabled_counterexample` shows that with the nonce check off, `reserved = [0,0]`.
- **Read depth:** `full`

### `ControlStack.Deployment.gate_contract`  — `ControlStack/Deployment/Contracts.lean:159`
- **Says (plain English):** Treat the SC26 model as an instance of the generic "gate" interface, where each step is an operation together with a proof that it is legal. Then after running any list of legal operations from the initial state: the SC26 invariant holds; the initial effect log (the bank) is a prefix of the final one (so the bank is append-only); and every bank entry is acceptable (has a request with that payload, is reserved, is approved by a non-requesting approver).
- **Under these hypotheses:** Operations are subtyped by `legal`, so each is individually legal. The model is `SC26.full`.
- **Does NOT say:** It adds no new safety content beyond `protocol_safe` and the invariant. The prefix fact is trivial from the initial state because the initial bank is empty. It says nothing about spend cap here (the cap is inside `Inv`, not in the stated acceptability predicate).
- **Kind:** `refinement/bridge` (an application of the generic `Spec.trace_safe` from `Core/Gate.lean` to SC26's `spec`).
- **Non-vacuity:** `Witnesses.gate_positive`.
- **Read depth:** `full`

### `ControlStack.Deployment.broker_contract`  — `ControlStack/Deployment/Contracts.lean:168`
- **Says (plain English):** In the SQLite-broker transition model (`TrustedBroker`), any state `t` reachable from the initial state with cap `cap` by any sequence of model steps is "Safe". Safe means four things: total spent is at most the cap; the number of releases is at most the amount spent; the list of consumed nonces has no repeats; and every lease's used amount is at most its budget.
- **Under these hypotheses:** `Trace R (initial cap) t`, a finite chain of `Step`s. Each step is one of: deny (no-op); stage an artifact (agent role); review (reviewer role, artifact exists); issue a lease (admin role); approve (approver role, matching review by a different reviewer, lease active, unexpired); revoke (admin); release (the `Allowed` guard); halt (admin). The `Roles` record carries a field `separated` saying no agent uid is a reviewer, approver or admin uid. That field is a **world assumption** supplied by whoever builds `R`. Time `now` is an arbitrary input (the docstring says no anti-rollback guarantee is inferred).
- **Does NOT say:** (a) Safe says nothing about approvals: it is a counting and uniqueness invariant, not "every release was approved/reviewed". (b) It says nothing about the sink or about any file. (c) It does not say the real SQLite database follows these steps (atomic storage, authentic OS identities and no rollback are listed as premises in the file header).
- **Kind:** `general theorem` (wrapper around `trace_preserves` with `initial_safe`).
- **Non-vacuity:** `Witnesses.useful_broker_trace` and `useful_broker_state` (a concrete six-step trace ending with `spent = 1`, `releases = 1`, `consumed = [7]`). `Witnesses.unguarded_release_refutes` shows a release without the guard violates Safe.
- **Read depth:** `full`

### `ControlStack.Deployment.deployment_safe`  — `ControlStack/Deployment/Contracts.lean:192`
- **Says (plain English):** Suppose the IR is accepted, the extracted graph is faithful, and the real sink publications are linked to the SC26 model by a `ProtocolRefinement`. Then four things hold. (1) Every real authority edge into the sink comes from the receiver. (2) Every published sink effect `(key, payload)` has a request with exactly that payload, its key is reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester. (3) The sink keys are all distinct. (4) The sum of published amounts is at most the cap, and the number of published effects is at most the cap.
- **Under these hypotheses:** `Accepted d` (the finite graph checks above). `ExtractionFaithful d r actualEdges`: every actual edge is in the IR, `r` is a node of the IR, and `r` is the receiver (a **world assumption**). `ProtocolRefinement d r R cap ops sinkEffects` has four fields, all **world assumptions** about the real system: (i) the model's gate credential equals the receiver's UID; (ii) every direct bank call in the model operation list carries the UID of some agent node; (iii) every published effect has amount exactly 1; (iv) the published sink effects are exactly equal (same list) to the bank ledger the model would produce when running `ops`. `ops` is a fixed list chosen by the theorem's caller.
- **Does NOT say:** (a) Conclusion (2) is not "the sink has no file except from a reviewed approval": SC26 has no reviewer. The approver is anyone in the approvers list who is not the requester, and there is no premise that approvers are distinct from agent UIDs. (b) The linkage from the real sink to the model is the hypothesis `publication` (equality of the real effects and the model's bank). It is assumed, not derived; if the real sink differs, nothing follows. (c) It holds for the one operation list `ops`, which must be the true history. The theorem does not show that any real behaviour corresponds to some `ops`. (d) Conclusion (4)'s length bound uses the assumed unit-cost field.
- **Kind:** `refinement/bridge` (conditional composition of `exclusive_sink`, `agent_not_receiver_uid`, `protocol_safe`).
- **Non-vacuity:** `Witnesses.useful_sc26_deployment_count` instantiates all hypotheses on `clean` (cap 1, one honest request) and extracts the length bound. Caveat: that witness's caller-binding hypothesis holds vacuously because its operation list contains no `bankCall`.
- **Read depth:** `full`

### `ControlStack.Deployment.accepted_no_avoided_path`  — `ControlStack/Deployment/R2Contracts.lean:20`
- **Says (plain English):** If the IR is accepted, then for every agent node `a`, there is no "avoided path" from `a` to the sink and none to the database. An avoided path is a chain of edges, starting at `a` and following any listed edges (authority-flagged or not), where no step lands on the broker or the receiver.
- **Under these hypotheses:** `Accepted d` and `a` an agent node of the IR. Conditions on the model; the IR containing every real edge is the **world assumption** (`faithful_extraction`).
- **Does NOT say:** (a) It does not rule out real paths through the broker or receiver. Once a path would land on those, it is cut off by definition. Whether they forward only what they should is outside this theorem. (b) It does not rule out paths using edges not in the IR. (c) It says nothing about other kinds of channels (shared memory, signals) unless the extractor encoded them as edges.
- **Kind:** `general theorem` (an induction on the path, using the closure fact stored in the `bypass` field of `Accepted`; close to unpacking a hypothesis).
- **Non-vacuity:** `Witnesses.path_positive` (clean); `Witnesses.bypass_path_exists` shows an avoided path does exist in a modified IR with an extra agent-to-sink edge.
- **Read depth:** `full`

### `ControlStack.Deployment.accepted_path_safety_monotone`  — `ControlStack/Deployment/R2Contracts.lean:38`
- **Says (plain English):** If a larger IR is accepted, and a smaller IR `d` has the same nodes, same broker/receiver/sink/database ids and only a subset of the edges, then for every agent node of `d` there is no avoided path to the sink or the database in `d`. So dropping edges from an accepted graph cannot create a bypass path.
- **Under these hypotheses:** Edge-subset inclusion; equality of node lists and of the four distinguished ids; `Accepted larger`. Conditions on the model.
- **Does NOT say:** (a) It does not say that `d` is itself `Accepted`. The next theorem shows an edge-dropped IR can fail `Accepted`. (b) It says nothing about the real system unless `d` is the true edge set and `larger` is a superset the user can vouch for. (c) It is about the path property only, not the other clauses of `Accepted`.
- **Kind:** `general theorem` (composes `accepted_no_avoided_path` with `path_edge_subset`).
- **Non-vacuity:** NOT SHOWN as a separate witness (instances hold by taking `d = larger = clean`, e.g. via `Witnesses.path_positive`, but there is no named strict-subset instance).
- **Read depth:** `full`

### `ControlStack.Deployment.path_edge_subset`  — `ControlStack/Deployment/R2Contracts.lean:27`
- **Says (plain English):** If every edge of `d` is also an edge of `larger`, and both have the same broker and receiver, then any avoided path in `d` from `start` to `target` is also an avoided path in `larger`.
- **Under these hypotheses:** Edge inclusion and equality of the broker and receiver ids. Conditions on the model.
- **Does NOT say:** It says nothing about acceptance or about the sink or database. Paths in `larger` may exist that are not in `d`.
- **Kind:** `general theorem` (a routine induction on the path).
- **Non-vacuity:** NOT SHOWN as a standalone example (it is a lemma; it is used in `accepted_path_safety_monotone`).
- **Read depth:** `full`

### `ControlStack.Deployment.requested_monotonicity_counterexample`  — `ControlStack/Deployment/R2Contracts.lean:53`
- **Says (plain English):** A concrete finite check. The IR `sinkOnly` has the same nodes as `clean`; every edge of `sinkOnly` is an edge of `clean`; it still contains the receiver's write edge into the sink; `clean` is accepted; but `sinkOnly` is not accepted. So "Accepted" is not preserved when edges are removed (it also demands that the broker and receiver database-write edges be present).
- **Under these hypotheses:** None (closed statement about two named IRs).
- **Does NOT say:** It does not say removing edges is unsafe: path-safety is monotone (see `accepted_path_safety_monotone`). It says only that the acceptance predicate, which includes positive existence requirements, is not monotone. Practically, an extraction that misses the database-write edges fails closed.
- **Kind:** `negative control (shows a weakened model fails)` computed by `decide` (a finite computation).
- **Non-vacuity:** It is itself a concrete witness; the statement is closed and checked by `decide`. The companions `missing_broker_writer_counterexample` and `missing_receiver_writer_counterexample` do the same for each write edge.
- **Read depth:** `full`

### `ControlStack.Deployment.deployment_broker_safe`  — `ControlStack/Deployment/R2Contracts.lean:101`
- **Says (plain English):** Suppose the IR is accepted, the extraction is faithful, and the real sink is linked to the broker model by a `BrokerProtocolRefinement`. Then: (1) every real authority edge into the sink comes from the receiver; (2) the receiver's UID is not an agent UID under the broker's role record; (3) the list of nonces published at the sink has no repeats; (4) the number of published nonces is at most the cap; (5) for each published nonce, the broker's final state holds an approval record under that nonce that is marked used.
- **Under these hypotheses:** `Accepted d`; `ExtractionFaithful d r actualEdges` (a **world assumption**: faithful extraction, the receiver node is identified). `BrokerProtocolRefinement d R cap t sinkNonces` has three fields: (i) `transactions`: the broker state `t` is reached from the initial state with cap `cap` by a trace of model steps (**world assumption**: the real broker's database history is such a trace); (ii) `callerBinding`: every UID that the roles record calls an agent is the UID of some agent node in the IR (**world assumption**); (iii) `publication`: the list of sink nonces, reversed, is a sublist of the broker's consumed-nonce list (**world assumption**: every file at the sink corresponds to a broker release, in admission order; the source says publication may lag admission). The broker's `Roles.separated` field is also assumed by whoever builds `R`.
- **Does NOT say:** (a) Conclusion (5) says an approval record under that nonce exists and is marked used. It does not say who signed it, that its digest matches the file at the sink, that its destination matches, or that the artifact was reviewed. Those conditions are part of the broker's release guard, but they are not stated in this conclusion. (b) The sink-to-broker link (`publication`) is a hypothesis; the theorem does not derive from the model that a file in the sink must have been released. Items (3), (4) and (5) follow from that hypothesis together with the broker invariants. (c) The bound (4) is on the total number of releases under the shared cap; per-agent lease budgets are in the broker's Safe invariant but are not part of this conclusion.
- **Kind:** `refinement/bridge`
- **Non-vacuity:** `Witnesses.useful_deployment_broker` instantiates it on `clean` with a concrete trace (cap 1, one release, nonce 7). `Witnesses.extracted` and `Witnesses.refined` supply the hypotheses. Hand-authored; the file notes these are "not observed container receipts".
- **Read depth:** `full`

### `ControlStack.Deployment.indexed_receipts_sound`  — `ControlStack/Deployment/R2Contracts.lean:146`
- **Says (plain English):** Suppose a table assigns each of the abstract state ids a complete broker state (`interpret`), has a step function on ids, and every step of the table is a legal broker `Step` between the interpreted states (`checked`). Then if the replay checker `verified` accepts a list of receipts starting from id `start`, the interpreted states form a broker `Trace` from the start state to the interpreted last recorded state.
- **Under these hypotheses:** `IndexedBrokerTable R` is supplied: for every id and every operation, `Step R (interpret s) (interpret (step s op))` is a proof. That is checked in Lean for each concrete table, but it requires such a table to exist for the transcript. `verified table.step start rs = true`: each receipt's `before` is the running id and its `after` equals the table's step.
- **Does NOT say:** (a) It does not say the receipts are real, complete or in the order the broker actually ran them. (b) It says nothing about the sink. (c) A shorter list also passes (see `omitted_tail_is_accepted`).
- **Kind:** `general theorem` (an induction over the receipt list).
- **Non-vacuity:** `Witnesses.indexed_positive` with `singleTable`, and `TranscriptReplay.table`.
- **Read depth:** `full`

### `ControlStack.TrustedBroker.transaction_preserves`  — `ControlStack/TrustedBroker.lean:158`
- **Says (plain English):** If a broker state `s` is Safe (spent at most cap; releases at most spent; consumed nonces distinct; every lease used at most its budget) and `t` is obtained from `s` by one model step, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Step roles s t`. The step guards (role checks, `Allowed` for release, lease validity on issue) are conditions of the model; they are the content of the proof. The proof for release uses that `Allowed` demands a positive cost, `used + cost <= budget`, `spent + cost <= cap` and that the nonce is not in the consumed list.
- **Does NOT say:** (a) Safe does not mention approvals, reviews, digests or destinations. (b) It does not cover any real transition that is not a `Step` (the model has no step that falsifies the `intact` flag, so tampering of staged bytes is outside it). (c) Time is an unconstrained input, so no clock-rollback protection follows.
- **Kind:** `general theorem` (one-step case analysis on the `Step` constructors).
- **Non-vacuity:** `Witnesses.useful_broker_trace`; the `Safe` hypothesis holds initially by `initial_safe`.
- **Read depth:** `full`

### `ControlStack.TrustedBroker.transaction_coherent`  — `ControlStack/TrustedBroker.lean:201`
- **Says (plain English):** Call a broker state "coherent" when a nonce is in the consumed-history list exactly when the approval stored under that nonce exists and is marked used. A single model step preserves coherence.
- **Under these hypotheses:** `Coherent s` and `Step roles s t`. For the approve step the proof uses that the nonce was fresh and the new approval is unused; for release both the history and the flag are updated together.
- **Does NOT say:** It does not say the real database's `used` column and any log agree; it is only about the two fields of the model state. It is a supporting invariant (it is what lets the main theorem turn "nonce is in consumed" into "approval is used").
- **Kind:** `general theorem` (one-step case analysis).
- **Non-vacuity:** `initial_coherent` and `Witnesses.useful_broker_trace` (coherence holds along it by `trace_coherent`).
- **Read depth:** `full`

### `ControlStack.TrustedBroker.halted_absorbing`  — `ControlStack/TrustedBroker.lean:196`
- **Says (plain English):** If a broker state is halted and one model step is taken, the result is still halted and the release counter has not changed.
- **Under these hypotheses:** `s.halted = true` and `Step roles s t`. The proof relies on every constructor except `deny` and `halt` requiring `halted = false` (including `release` via `Allowed`).
- **Does NOT say:** (a) It does not say the whole state is unchanged, only the halted flag and the release count. (b) It does not say a halt is ever processed (no liveness). (c) The `halt` step can be issued only by an admin, and the model has no step that clears the flag; that is a feature of the model, not something the real database enforces.
- **Kind:** `general theorem` (one-step case analysis).
- **Non-vacuity:** NOT SHOWN as a named instance in the files read (no halted state appears in the witnesses; the hypothesis is satisfiable by the `halt` step from any state).
- **Read depth:** `full`

### `ControlStack.TrustedBroker.committed_nonce_unusable`  — `ControlStack/TrustedBroker.lean:112`
- **Says (plain English):** For any state `s` and any release `(r, a, l)`, after applying the release (the function `committed`), no request `r'` with the same nonce as `r` can satisfy the release guard `Allowed`, whatever approval, lease or clock value is offered.
- **Under these hypotheses:** None beyond `r'.nonce = r.nonce`. The statement does not require that the release itself was Allowed in `s`. The proof uses the fact that `committed` stores the approval under the nonce with `used = true`, while `Allowed` requires the approval to have `used = false`.
- **Does NOT say:** (a) A different nonce for the same digest can be approved and released again (limited only by lease and global budget). (b) It is not about the sink; one nonce yields at most one broker release, not "one file". (c) It depends on the guard reading the stored `used` flag; whether the real SQL does so is part of the refinement assumption.
- **Kind:** `general theorem` (almost direct from the definition of `committed`; trivial in proof effort).
- **Non-vacuity:** `Witnesses.replay_refuted` and `TranscriptReplay.replay_was_not_allowed` are instances.
- **Read depth:** `full`

### `ControlStack.TrustedBroker.trace_preserves`  — `ControlStack/TrustedBroker.lean:233`
- **Says (plain English):** If a state `s` is Safe and `t` is reachable from `s` by any finite sequence of model steps, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Trace roles s t`.
- **Does NOT say:** Same limits as `transaction_preserves`: no approval, review or sink content; model steps only. The trace relation includes any serial order of committed transactions but "excludes snapshot rollback and partial external effects" by construction, so a real rollback is outside the model.
- **Kind:** `general theorem` (induction over the trace from `transaction_preserves`).
- **Non-vacuity:** `Witnesses.useful_broker_trace`; initial state Safe by `initial_safe`.
- **Read depth:** `full`

### `ControlStack.Deployment.TranscriptReplay.runtime_trace`  — `ControlStack/Deployment/TranscriptReplay.lean:108`
- **Says (plain English):** There is a chain of ten broker model steps from the initial state with cap 2 to the specific state `s10`. The ten steps are, in order: stage artifact 1; review it; issue lease 1; approve nonce 1; stage by the second agent; issue lease 2; approve nonce 2; release nonce 1; a denial; release nonce 2.
- **Under these hypotheses:** None as a statement. The proof builds the ten steps by hand (each by `ok`/`decide`) and shows the receipt list passes the replay checker. What it means for the real run depends on a premise that is not proved: that the recorded request/response log (hash cited in the file header) is genuine, complete, in the real order, and that each recorded response corresponds to the model step it was mapped to.
- **Does NOT say:** (a) It does not say the real run is this trace. It says this trace is valid in the model. The mapping from the log to the steps was done by a generator script. (b) The recorded `now` is a single value (the release timestamp from the database) used for every step, though the file notes issue/approve requests were made earlier. (c) Nothing links the model releases to files at the sink; that link is the receiver refinement premise, checked separately on bytes. (d) A denied response is modelled as an identity step, which any denial would satisfy, whatever the reason.
- **Kind:** `finite computation (decide/native)` plus `refinement/bridge` (a concrete chain, checked by `decide` through `indexed_receipts_sound`).
- **Non-vacuity:** The statement is a concrete existence claim, constructed explicitly from `tx0..tx9`; it is its own witness.
- **Read depth:** `full`

### `ControlStack.Deployment.TranscriptReplay.final_safe`  — `ControlStack/Deployment/TranscriptReplay.lean:113`
- **Says (plain English):** The final model state `s10` of the replayed transcript is Safe: spent (2) is at most cap (2); releases at most spent; consumed nonces distinct; every lease within budget.
- **Under these hypotheses:** None as a statement; it follows from `runtime_trace` plus `trace_preserves`. The same caveats as `runtime_trace` about whether the recorded log is the true run apply.
- **Does NOT say:** (a) It says nothing about the real database or sink, only about the model state obtained from the transcript. (b) Safe does not include any approval or review facts. (c) It does not show the transcript is complete: the omission examples show that a truncated transcript also passes.
- **Kind:** `finite computation (decide/native)` for the instance (derived from the general `trace_preserves`).
- **Non-vacuity:** Concrete; `final_counts` (in the same file, not translated here) records `cap = 2`, `spent = 2`, `releases = 2`, `consumed = [2, 1]`, `halted = false`.
- **Read depth:** `full`

### `ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed`  — `ControlStack/Deployment/TranscriptReplay.lean:125`
- **Says (plain English):** In the model state `s8` reached just after the first release (nonce 1), the request `q8` (which has the same fields as the first release's request, so the same nonce) fails the release guard, whatever clock value, approval record and lease are offered. That is the model's explanation of the recorded denial in step 8.
- **Under these hypotheses:** None beyond the definitions; it quantifies over every clock value `now`, approval `a'` and lease `l'`.
- **Does NOT say:** (a) It does not show the real broker denied the real replay for this reason; the checker takes any recorded denial as an identity step. (b) It does not exclude replays under a different nonce. (c) It is a consequence of `committed_nonce_unusable`.
- **Kind:** `definitional/trivial` (a direct instance of `committed_nonce_unusable`, closed by `rfl`).
- **Non-vacuity:** Concrete instance on `s8`.
- **Read depth:** `full`

### `ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted`  — `ControlStack/Deployment/TranscriptReplay.lean:137`
- **Says (plain English):** The replay checker also accepts the transcript with its last receipt (the second release) removed: the first nine receipts form a valid shorter chain. A companion theorem (not translated here) says the end state then differs from the full one.
- **Under these hypotheses:** None (a closed finite computation by `decide`).
- **Does NOT say:** It is a limitation, not a safety claim: the checker verifies the chain but not completeness. A transcript that omits trailing events is indistinguishable by this checker from a complete one. It also is not a claim that this particular truncation happened.
- **Kind:** `negative control (shows a weakened model fails)` (more precisely, it demonstrates a blind spot of the replay checker), also `finite computation (decide/native)`.
- **Non-vacuity:** Closed statement; it is itself the concrete example.
- **Read depth:** `full`
