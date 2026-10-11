# Blind semantic target 16: ControlStack.Deployment.deployment_broker_safe

∀ d r R cap t sinkNonces actualEdges, Accepted d → ExtractionFaithful d r actualEdges → BrokerProtocolRefinement d R cap t sinkNonces → sinkNonces.length < cap ∧ sinkNonces.Nodup ∧ (∀ nonce ∈ sinkNonces, ∃ approval, t.approvals nonce = some approval ∧ approval.used = true) ∧ exclusive actual sink ∧ receiverUIDnotAgent R r

## English under test

`ControlStack.Deployment.deployment_broker_safe`  — `ControlStack/Deployment/R2Contracts.lean:101`
- **Says (plain English):** For an accepted deployment with faithful extraction and protocol refinement, the number of published nonces is strictly less than the cap, there are no duplicates, and every published nonce has an approval marked used; also actual authority edges into the sink come from the receiver and the receiver UID is not an agent UID.
- **Under these hypotheses:** `Accepted d`; `ExtractionFaithful d r actualEdges` (a **world assumption**: faithful extraction, the receiver node is identified). `BrokerProtocolRefinement d R cap t sinkNonces` has three fields: (i) `transactions`: the broker state `t` is reached from the initial state with cap `cap` by a trace of model steps (**world assumption**: the real broker's database history is such a trace); (ii) `callerBinding`: every UID that the roles record calls an agent is the UID of some agent node in the IR (**world assumption**); (iii) `publication`: the list of sink nonces, reversed, is a sublist of the broker's consumed-nonce list (**world assumption**: every file at the sink corresponds to a broker release, in admission order; the source says publication may lag admission). The broker's `Roles.separated` field is also assumed by whoever builds `R`.

