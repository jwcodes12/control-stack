# SC-17: catalog draft

**Bad event:** Agent sabotages IaC, Kubernetes or production cluster permissions

**Candidate policy/invariant:** Enforce declarative policy invariants on resource graphs and diff; deny unauthorized apply operations

**Reusable proof/checker blocks:** F1, F3, F4

**Threat source:** ControlArena IaC / Infra

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent sabotages IaC, Kubernetes or production cluster permissions

**Honest usefulness:** no fixture selected, no completion measured.
