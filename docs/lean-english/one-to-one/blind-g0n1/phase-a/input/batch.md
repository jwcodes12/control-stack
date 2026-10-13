# English statements under test

### Claim 1
## `ControlStack.Deployment.runtime_exclusive`

- **Says (plain English):** If the configuration is accepted, and every edge in a list `actual` of real, observed authority edges is also in the IR, then every real authority edge into the sink comes from the receiver.
- **Under these hypotheses:** `Accepted d`, and `Faithful d actual`. The latter is a structure with one field: every edge in `actual` is a member of `d.edges`. This second hypothesis is a **world assumption** (that observed runtime edges are included in the extraction). The source describes it as "the residual implementation/environment premise, not kernel-proved". The edge `e` in question must be in `actual` and be marked `authority = true` with target the sink.
- **Does NOT say:** (a) It does not show that `actual` is the complete list of real edges. Faithfulness is only "everything in `actual` is in the IR", and `actual` is whatever the caller supplies. (b) The name "runtime" is about the premise, not about monitoring anything at runtime. (c) It adds nothing to `exclusive_sink` beyond composing it with the inclusion hypothesis.
- **Kind:** `definitional/trivial` (`exclusive_sink` applied to a member of `d.edges`).

### Claim 2
## `ControlStack.Deployment.agent_call_legal`

- **Says (plain English):** For an accepted deployment, a direct call to the external system (the "bank"/sink service) made under an agent node's UID is a "legal" operation of the SC26 model. In that model "legal" means the caller does not carry the gate's own credential. The role record is built so that the gate credential equals the receiver node's UID.
- **Under these hypotheses:** `Accepted d`; `r` is the receiver node and `a` an agent node in `d.nodes`. `approvers` and `admins` are arbitrary lists: the roles function only fills the agent-UID list from the IR, and nothing is required of the approver or admin lists (they may overlap agent UIDs). The identification "SC26 gate credential = receiver's UID" is part of how `roles` is defined and is a modelling choice that must be borne out in the real system. The comment in the source says role IDs and actual SO_PEERCRED bindings are residual.
- **Does NOT say:** (a) It does not say the agent cannot call the bank or the sink; it says that in the model the call carries a non-gate credential, and the model's bank rejects such calls. That rejection is built into the SC26 step function. (b) It does not say anything about approver or admin credential separation. (c) It does not establish that the real sink service authenticates by UID.
- **Kind:** `definitional/trivial` (it is `agent_not_receiver_uid` re-read through the definitions of `legal` and `roles`).

### Claim 3
## `ControlStack.Deployment.protocol_safe`

- **Says (plain English):** In the SC26 gate-and-bank model, start from the empty state and run any finite sequence of operations (requests, approvals, executions, delivery retries, message arrivals, direct bank calls, halts), as long as no direct bank call carries the gate's credential. Then in the final state: (1) every entry in the bank has a stored request with exactly that payload, the request id has been reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester; (2) bank keys are all distinct; (3) the sum of the bank entries' amounts is at most the cap.
- **Under these hypotheses:** Every operation in the list is `legal` (the only restriction is that a `bankCall` is not made with the gate's credential; all other operations are unrestricted). The model's checks are all enabled (`SC26.full`): approval distinctness, payload-exact approval, nonce guard, cap guard, halt check, bank deduplication, bank authentication. The roles record `R` (agents, approvers, admins, gate credential) and `cap` are arbitrary.
- **Does NOT say:** (a) There is no review step in SC26. "Approved" means an entry in the approvers list that differs from the requester; it does not include any independent reviewer of the artifact. (b) Nothing assures that the approvers are not also agents: that requires a separate disjointness hypothesis (`sc26_safe_disjoint`), not used here. An `approve` carrying an approver identity is treated as that approver's genuine act. (c) Exactly-once is per request id, not per business intent: the same payload requested twice can be paid twice. (d) It is a statement about the abstract model, not the Python.
- **Kind:** `general theorem` (a one-line wrapper of `SC26.sc26_safe`, whose proof is an induction over operation lists using the invariant `SC26.Inv`).

### Claim 4
## `ControlStack.Deployment.one_use`

- **Says (plain English):** In the SC26 model with all checks on, after any finite sequence of operations at all (no legality premise), the list of reserved request ids contains no repeats. So each request id is reserved, and its amount is charged against the cap, at most once.
- **Under these hypotheses:** None beyond the model definition (the `execute` step refuses to reserve an id already in the reserved list when the nonce check is on, which it is in `full`). It holds for arbitrary roles, cap and operation list.
- **Does NOT say:** (a) It does not say the same payment cannot happen twice under two different request ids (separate requests with identical content are independent). (b) It concerns reservation inside the gate, not what reaches the sink. (c) It is about SC26's request ids, not about the broker model's nonces.
- **Kind:** `general theorem` (wrapper of `SC26.sc26_once`, an induction).

### Claim 5
## `ControlStack.Deployment.gate_contract`

- **Says (plain English):** Treat the SC26 model as an instance of the generic "gate" interface, where each step is an operation together with a proof that it is legal. Then after running any list of legal operations from the initial state: the SC26 invariant holds; the initial effect log (the bank) is a prefix of the final one (so the bank is append-only); and every bank entry is acceptable (has a request with that payload, is reserved, is approved by a non-requesting approver).
- **Under these hypotheses:** Operations are subtyped by `legal`, so each is individually legal. The model is `SC26.full`.
- **Does NOT say:** It adds no new safety content beyond `protocol_safe` and the invariant. The prefix fact is trivial from the initial state because the initial bank is empty. It says nothing about spend cap here (the cap is inside `Inv`, not in the stated acceptability predicate).
- **Kind:** `refinement/bridge` (an application of the generic `Spec.trace_safe` from `Core/Gate.lean` to SC26's `spec`).

### Claim 6
## `ControlStack.Deployment.broker_contract`

- **Says (plain English):** In the SQLite-broker transition model (`TrustedBroker`), any state `t` reachable from the initial state with cap `cap` by any sequence of model steps is "Safe". Safe means four things: total spent is at most the cap; the number of releases is at most the amount spent; the list of consumed nonces has no repeats; and every lease's used amount is at most its budget.
- **Under these hypotheses:** `Trace R (initial cap) t`, a finite chain of `Step`s. Each step is one of: deny (no-op); stage an artifact (agent role); review (reviewer role, artifact exists); issue a lease (admin role); approve (approver role, matching review by a different reviewer, lease active, unexpired); revoke (admin); release (the `Allowed` guard); halt (admin). The `Roles` record carries a field `separated` saying no agent uid is a reviewer, approver or admin uid. That field is a **world assumption** supplied by whoever builds `R`. Time `now` is an arbitrary input (the docstring says no anti-rollback guarantee is inferred).
- **Does NOT say:** (a) Safe says nothing about approvals: it is a counting and uniqueness invariant, not "every release was approved/reviewed". (b) It says nothing about the sink or about any file. (c) It does not say the real SQLite database follows these steps (atomic storage, authentic OS identities and no rollback are listed as premises in the file header).
- **Kind:** `general theorem` (wrapper around `trace_preserves` with `initial_safe`).

### Claim 7
## `ControlStack.Deployment.deployment_safe`

- **Says (plain English):** Suppose the IR is accepted, the extracted graph is faithful, and the real sink publications are linked to the SC26 model by a `ProtocolRefinement`. Then four things hold. (1) Every real authority edge into the sink comes from the receiver. (2) Every published sink effect `(key, payload)` has a request with exactly that payload, its key is reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester. (3) The sink keys are all distinct. (4) The sum of published amounts is at most the cap, and the number of published effects is at most the cap.
- **Under these hypotheses:** `Accepted d` (the finite graph checks above). `ExtractionFaithful d r actualEdges`: every actual edge is in the IR, `r` is a node of the IR, and `r` is the receiver (a **world assumption**). `ProtocolRefinement d r R cap ops sinkEffects` has four fields, all **world assumptions** about the real system: (i) the model's gate credential equals the receiver's UID; (ii) every direct bank call in the model operation list carries the UID of some agent node; (iii) every published effect has amount exactly 1; (iv) the published sink effects are exactly equal (same list) to the bank ledger the model would produce when running `ops`. `ops` is a fixed list chosen by the theorem's caller.
- **Does NOT say:** (a) Conclusion (2) is not "the sink has no file except from a reviewed approval": SC26 has no reviewer. The approver is anyone in the approvers list who is not the requester, and there is no premise that approvers are distinct from agent UIDs. (b) The linkage from the real sink to the model is the hypothesis `publication` (equality of the real effects and the model's bank). It is assumed, not derived; if the real sink differs, nothing follows. (c) It holds for the one operation list `ops`, which must be the true history. The theorem does not show that any real behaviour corresponds to some `ops`. (d) Conclusion (4)'s length bound uses the assumed unit-cost field.
- **Kind:** `refinement/bridge` (conditional composition of `exclusive_sink`, `agent_not_receiver_uid`, `protocol_safe`).

### Claim 8
## `ControlStack.Deployment.accepted_path_safety_monotone`

- **Says (plain English):** If a larger IR is accepted, and a smaller IR `d` has the same nodes, same broker/receiver/sink/database ids and only a subset of the edges, then for every agent node of `d` there is no avoided path to the sink or the database in `d`. So dropping edges from an accepted graph cannot create a bypass path.
- **Under these hypotheses:** Edge-subset inclusion; equality of node lists and of the four distinguished ids; `Accepted larger`. Conditions on the model.
- **Does NOT say:** (a) It does not say that `d` is itself `Accepted`. The next theorem shows an edge-dropped IR can fail `Accepted`. (b) It says nothing about the real system unless `d` is the true edge set and `larger` is a superset the user can vouch for. (c) It is about the path property only, not the other clauses of `Accepted`.
- **Kind:** `general theorem` (composes `accepted_no_avoided_path` with `path_edge_subset`).

### Claim 9
## `ControlStack.Deployment.path_edge_subset`

- **Says (plain English):** If every edge of `d` is also an edge of `larger`, and both have the same broker and receiver, then any avoided path in `d` from `start` to `target` is also an avoided path in `larger`.
- **Under these hypotheses:** Edge inclusion and equality of the broker and receiver ids. Conditions on the model.
- **Does NOT say:** It says nothing about acceptance or about the sink or database. Paths in `larger` may exist that are not in `d`.
- **Kind:** `general theorem` (a routine induction on the path).

### Claim 10
## `ControlStack.Deployment.requested_monotonicity_counterexample`

- **Says (plain English):** A concrete finite check. The IR `sinkOnly` has the same nodes as `clean`; every edge of `sinkOnly` is an edge of `clean`; it still contains the receiver's write edge into the sink; `clean` is accepted; but `sinkOnly` is not accepted. So "Accepted" is not preserved when edges are removed (it also demands that the broker and receiver database-write edges be present).
- **Under these hypotheses:** None (closed statement about two named IRs).
- **Does NOT say:** It does not say removing edges is unsafe: path-safety is monotone (see `accepted_path_safety_monotone`). It says only that the acceptance predicate, which includes positive existence requirements, is not monotone. Practically, an extraction that misses the database-write edges fails closed.
- **Kind:** `negative control (shows a weakened model fails)` computed by `decide` (a finite computation).
