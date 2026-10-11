# Blind semantic target 6: ControlStack.Deployment.agent_call_legal

∀ d r a approvers admins p, Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true → legal (roles d r approvers admins) (bankCall a.uid p)

## English under test

`ControlStack.Deployment.agent_call_legal`  — `ControlStack/Deployment/Contracts.lean:143`
- **Says (plain English):** For an accepted deployment, a direct call to the external system (the "bank"/sink service) made under an agent node's UID is a "legal" operation of the SC26 model. In that model "legal" means the caller does not carry the gate's own credential. The role record is built so that the gate credential equals the receiver node's UID.
- **Under these hypotheses:** `Accepted d`; `r` is the receiver node and `a` an agent node in `d.nodes`. `approvers` and `admins` are arbitrary lists: the roles function only fills the agent-UID list from the IR, and nothing is required of the approver or admin lists (they may overlap agent UIDs). The identification "SC26 gate credential = receiver's UID" is part of how `roles` is defined and is a modelling choice that must be borne out in the real system. The comment in the source says role IDs and actual SO_PEERCRED bindings are residual.

