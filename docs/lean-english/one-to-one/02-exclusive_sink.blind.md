# Blind semantic target 2: ControlStack.Deployment.exclusive_sink

∀ d e, Accepted d → e ∈ d.edges → e.authority = true → e.target = d.sink → (e.source = d.receiver ∨ e.source = d.broker)

## English under test

`ControlStack.Deployment.exclusive_sink`  — `ControlStack/Deployment/Contracts.lean:114`
- **Says (plain English):** For an accepted deployment, any edge in the IR that is marked as an authority edge and whose target is the sink has the receiver or the broker as its source.
- **Under these hypotheses:** `Accepted d`, and the edge is a member of `d.edges` with `authority = true` and `target = d.sink`. These are conditions on the model. The proof reads off the second clause of `BaseAccepted`.

