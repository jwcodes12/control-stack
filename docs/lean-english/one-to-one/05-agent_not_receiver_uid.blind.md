# Blind semantic target 5: ControlStack.Deployment.agent_not_receiver_uid

∀ d r, Accepted d → r ∈ d.nodes → r.id = d.receiver → ∀ a ∈ d.nodes, a.uid ≠ r.uid. Literal Says quantifies all nodes; Under narrows a to agents. Record both interpretations.

## English under test

`ControlStack.Deployment.agent_not_receiver_uid`  — `ControlStack/Deployment/Contracts.lean:134`
- **Says (plain English):** If the configuration is accepted, then no node in the IR has the same UID as the node that is the receiver.
- **Under these hypotheses:** `Accepted d`; `r` is a node in the IR with id equal to the receiver id; `a` is a node in the IR with `agent = true`. Conditions on the model. That the Compose-reported UIDs are the real process UIDs is the **world assumption** (`tcb`, `faithful_extraction`).

