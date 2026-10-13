# English statements under test (batch: stale G0 rows)

## Claim 1: `ControlStack.Deployment.Accepted`

- **Says (plain English):** This is a definition, not a theorem. A deployment description `d` (a list of nodes, a list of edges, and the identities of the receiver, broker, sink and database) is "accepted" when six groups of finite checks all pass.
  1. *Basic.* Every edge is a known edge. Every edge marked "authority" that targets the sink comes from the receiver. Every authority edge that targets the database comes from the receiver or the broker. No node is privileged or on the host network. No agent node has the receiver's UID. The receiver has an authority edge to the sink. Every UID is positive, i.e. nobody is root.
  2. *Roles.* There are exactly six nodes: two agents, one broker, one receiver, one reviewer and one approver. A node is an agent exactly when its role number is 0. It is the broker exactly when its id is the broker id and its role is 1, and likewise for the receiver and role 2.
  3. *Identities.* For any pair of distinct nodes, their UIDs are equal **if and only if** they are the broker and receiver (in either order); all other distinct node pairs have different UIDs.
  4. *Runtime.* Every node's `runtimeMatch` flag is true.
  5. *Writers.* Every edge, authority-marked or not, that targets the sink goes from the receiver and is a write edge. The set of write edges into the sink has exactly the receiver as its source list. Every edge into the database comes from the broker or receiver. There are exactly two write edges into the database, one from the broker and one from the receiver.
  6. *No-bypass.* For every agent node `a`: the set `reachable d a.id` (computed by following every edge except edges that land on the broker or receiver) does not contain the sink or the database. That set is also closed under such edges.
- **Under these hypotheses:** None; it is a predicate on a finite structure. The inputs it reads (`authority`, `unknown`, `write` flags on edges; `agent`, `privileged`, `hostNetwork`, `role`, `runtimeMatch` flags and UIDs on nodes) are produced by an extractor from Compose and the daemon inventory. That the extractor tells the truth is a **world assumption** (`faithful_extraction`, `tcb`). The `runtimeMatch` flags are, in the source's own words, "input observations, not independent attestation".
- **Does NOT say:** (a) Nothing about the Python code, the kernel, or what the broker or receiver actually do. Edges that land on the broker or receiver are treated as mediated and are not examined further. (b) It does not say the configuration is complete: an authority path through an edge the extractor did not list is invisible. (c) It fixes the topology to exactly six nodes (two agents), so it is not a general checker for other deployments.
- **Kind:** `definitional/trivial` (a definition; its decidability instance is by `infer_instance`).

## Claim 2: `ControlStack.Deployment.exclusive_sink`

- **Says (plain English):** For an accepted deployment, any edge in the IR that is marked as an authority edge and whose target is the sink has the receiver as its source. So, as far as the IR lists, only the receiver holds authority over the sink.
- **Under these hypotheses:** `Accepted d`, and the edge is a member of `d.edges` with `authority = true` and `target = d.sink`. These are conditions on the model. The proof reads off the second clause of `BaseAccepted`.
- **Does NOT say:** (a) It does not say that no real process other than the receiver can write to the real sink. That needs the IR to contain all real authority edges (an unproved assumption, `faithful_extraction`). (b) It covers only edges flagged `authority = true`. The stronger "every edge, flagged or not, into the sink comes from the receiver" fact lives in the writers check but is not what this theorem states. (c) It says nothing about what the receiver writes.
- **Kind:** `definitional/trivial` (a projection of a field of `Accepted`).

## Claim 3: `ControlStack.Deployment.database_custody`

- **Says (plain English):** For an accepted deployment, any authority edge in the IR that targets the database has the receiver or the broker as its source.
- **Under these hypotheses:** `Accepted d`, plus the edge being in `d.edges`, marked authority, targeting `d.database`. Conditions on the model.
- **Does NOT say:** (a) The database is not protected against the broker or receiver themselves. (b) It does not say real agents have no real path to the database; it holds only relative to the IR. (c) It says nothing about which of the two (broker or receiver) wrote what.
- **Kind:** `definitional/trivial` (a projection of the third clause of `BaseAccepted`).

## Claim 5: `ControlStack.Deployment.agent_not_receiver_uid`

- **Says (plain English):** If the configuration is accepted, then no node flagged as an agent has the same UID as the node that is the receiver. So an agent cannot carry the receiver's operating-system identity.
- **Under these hypotheses:** `Accepted d`; `r` is a node in the IR with id equal to the receiver id; `a` is a node in the IR with `agent = true`. Conditions on the model. That the Compose-reported UIDs are the real process UIDs is the **world assumption** (`tcb`, `faithful_extraction`).
- **Does NOT say:** (a) It does not say an agent cannot act as the receiver by other means (stolen credentials, shared files, ptrace, etc.). Only the UID field is compared. (b) It does not say the broker is separate from the receiver. In `clean` and in the `Accepted` identity check, the broker and receiver deliberately share one UID. (c) It does not say agents are distinct from each other.
- **Kind:** `definitional/trivial` (a projection of the fifth clause of `BaseAccepted`).

## Claim 12: `ControlStack.Deployment.accepted_no_avoided_path`

- **Says (plain English):** If the IR is accepted, then for every agent node `a`, there is no "avoided path" from `a` to the sink and none to the database. An avoided path is a chain of edges, starting at `a` and following any listed edges (authority-flagged or not), where no step lands on the broker or the receiver.
- **Under these hypotheses:** `Accepted d` and `a` an agent node of the IR. Conditions on the model; the IR containing every real edge is the **world assumption** (`faithful_extraction`).
- **Does NOT say:** (a) It does not rule out real paths through the broker or receiver. Once a path would land on those, it is cut off by definition. Whether they forward only what they should is outside this theorem. (b) It does not rule out paths using edges not in the IR. (c) It says nothing about other kinds of channels (shared memory, signals) unless the extractor encoded them as edges.
- **Kind:** `general theorem` (an induction on the path, using the closure fact stored in the `bypass` field of `Accepted`; close to unpacking a hypothesis).

## Claim 16: `ControlStack.Deployment.deployment_broker_safe`

- **Says (plain English):** Suppose the IR is accepted, the extraction is faithful, and the real sink is linked to the broker model by a `BrokerProtocolRefinement`. Then: (1) every real authority edge into the sink comes from the receiver; (2) the receiver's UID is not an agent UID under the broker's role record; (3) the list of nonces published at the sink has no repeats; (4) the number of published nonces is at most the cap; (5) for each published nonce, the broker's final state holds an approval record under that nonce that is marked used.
- **Under these hypotheses:** `Accepted d`; `ExtractionFaithful d r actualEdges` (a **world assumption**: faithful extraction, the receiver node is identified). `BrokerProtocolRefinement d R cap t sinkNonces` has three fields: (i) `transactions`: the broker state `t` is reached from the initial state with cap `cap` by a trace of model steps (**world assumption**: the real broker's database history is such a trace); (ii) `callerBinding`: every UID that the roles record calls an agent is the UID of some agent node in the IR (**world assumption**); (iii) `publication`: the list of sink nonces, reversed, is a sublist of the broker's consumed-nonce list (**world assumption**: every file at the sink corresponds to a broker release, in admission order; the source says publication may lag admission). The broker's `Roles.separated` field is also assumed by whoever builds `R`.
- **Does NOT say:** (a) Conclusion (5) says an approval record under that nonce exists and is marked used. It does not say who signed it, that its digest matches the file at the sink, that its destination matches, or that the artifact was reviewed. Those conditions are part of the broker's release guard, but they are not stated in this conclusion. (b) The sink-to-broker link (`publication`) is a hypothesis; the theorem does not derive from the model that a file in the sink must have been released. Items (3), (4) and (5) follow from that hypothesis together with the broker invariants. (c) The bound (4) is on the total number of releases under the shared cap; per-agent lease budgets are in the broker's Safe invariant but are not part of this conclusion.
- **Kind:** `refinement/bridge`

## Claim 20: `ControlStack.TrustedBroker.halted_absorbing`

- **Says (plain English):** If a broker state is halted and one model step is taken, the result is still halted and the release counter has not changed.
- **Under these hypotheses:** `s.halted = true` and `Step roles s t`. The proof relies on every constructor except `deny` and `halt` requiring `halted = false` (including `release` via `Allowed`).
- **Does NOT say:** (a) It does not say the whole state is unchanged, only the halted flag and the release count. (b) It does not say a halt is ever processed (no liveness). (c) The `halt` step can be issued only by an admin, and the model has no step that clears the flag; that is a feature of the model, not something the real database enforces.
- **Kind:** `general theorem` (one-step case analysis).

## Claim 23: `ControlStack.Deployment.TranscriptReplay.runtime_trace`

- **Says (plain English):** The theorem asserts only that a broker-model trace connects the cap-2 initial state to `s10`. Its proof constructs this particular trace using ten ordered receipts: stage artifact 1; review it; issue lease 1; approve nonce 1; stage by the second agent; issue lease 2; approve nonce 2; release nonce 1; a denial; release nonce 2. The theorem statement does **not** quantify or establish that every such trace has ten steps, that the real execution followed this order, or that a runtime log is complete.
- **Under these hypotheses:** None as a statement. The proof builds the ten steps by hand (each by `ok`/`decide`) and shows the receipt list passes the replay checker. What it means for the real run depends on a premise that is not proved: that the recorded request/response log (hash cited in the file header) is genuine, complete, in the real order, and that each recorded response corresponds to the model step it was mapped to.
- **Does NOT say:** (a) It does not say the real run is this trace. It says this trace is valid in the model. The mapping from the log to the steps was done by a generator script. (b) The recorded `now` is a single value (the release timestamp from the database) used for every step, though the file notes issue/approve requests were made earlier. (c) Nothing links the model releases to files at the sink; that link is the receiver refinement premise, checked separately on bytes. (d) A denied response is modelled as an identity step, which any denial would satisfy, whatever the reason.
- **Kind:** `finite computation (decide/native)` plus `refinement/bridge` (a concrete chain, checked by `decide` through `indexed_receipts_sound`).
