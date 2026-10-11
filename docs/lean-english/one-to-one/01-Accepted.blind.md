# Blind semantic target 1: ControlStack.Deployment.Accepted

Accepted means Basic AND Roles AND Identities AND Runtime AND Writers AND NoBypass, with the checks listed verbatim in the input. Expand these independently; do not alias Accepted.

## English under test

`ControlStack.Deployment.Accepted`  — `ControlStack/Deployment/Contracts.lean:99`
- **Says (plain English):** This is a definition, not a theorem. A deployment description `d` (a list of nodes, a list of edges, and the identities of the receiver, broker, sink and database) is "accepted" when six groups of finite checks all pass.
  1. *Basic.* Every edge is a known edge. Every edge marked "authority" that targets the sink comes from the receiver. Every authority edge that targets the database comes from the receiver or the broker. No node is privileged or on the host network. No agent node has the receiver's UID. The receiver has an authority edge to the sink. Every UID is positive, i.e. nobody is root.
  2. *Roles.* There are exactly six nodes: two agents, one broker, one receiver, one reviewer and one approver. A node is an agent exactly when its role number is 0. It is the broker exactly when its id is the broker id and its role is 1, and likewise for the receiver and role 2.
  3. *Identities.* Two distinct nodes share a UID only if they are the broker and the receiver. Every other UID is unique.
  4. *Runtime.* Every node's `runtimeMatch` flag is true.
  5. *Writers.* Every edge, authority-marked or not, that targets the sink goes from the receiver and is a write edge. The set of write edges into the sink has exactly the receiver as its source list. Every edge into the database comes from the broker or receiver. There are exactly two write edges into the database, one from the broker and one from the receiver.
  6. *No-bypass.* For every agent node `a`: the set `reachable d a.id` (computed by following every edge except edges that land on the broker or receiver) does not contain the sink or the database. That set is also closed under such edges.
- **Under these hypotheses:** None; it is a predicate on a finite structure. The inputs it reads (`authority`, `unknown`, `write` flags on edges; `agent`, `privileged`, `hostNetwork`, `role`, `runtimeMatch` flags and UIDs on nodes) are produced by an extractor from Compose and the daemon inventory. That the extractor tells the truth is a **world assumption** (`faithful_extraction`, `tcb`). The `runtimeMatch` flags are, in the source's own words, "input observations, not independent attestation".

