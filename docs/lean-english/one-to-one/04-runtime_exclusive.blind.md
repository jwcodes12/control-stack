# Blind semantic target 4: ControlStack.Deployment.runtime_exclusive

∀ d actual e, Accepted d → Faithful d actual → e ∈ actual → e.authority = true → e.target = d.sink → e.source = d.receiver

## English under test

`ControlStack.Deployment.runtime_exclusive`  — `ControlStack/Deployment/Contracts.lean:128`
- **Says (plain English):** If the configuration is accepted, and every edge in a list `actual` of real, observed authority edges is also in the IR, then every real authority edge into the sink comes from the receiver.
- **Under these hypotheses:** `Accepted d`, and `Faithful d actual`. The latter is a structure with one field: every edge in `actual` is a member of `d.edges`. This second hypothesis is a **world assumption** (that observed runtime edges are included in the extraction). The source describes it as "the residual implementation/environment premise, not kernel-proved". The edge `e` in question must be in `actual` and be marked `authority = true` with target the sink.

