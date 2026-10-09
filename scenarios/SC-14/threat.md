# SC-14: catalog draft

**Bad event:** Agent consumes runaway compute, tokens, network or budget

**Candidate policy/invariant:** Cumulative trusted quotas across workers; enforced kill/expiry; restart-safe counters

**Reusable proof/checker blocks:** F3, F5

**Threat source:** General control infrastructure

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent consumes runaway compute, tokens, network or budget

**Honest usefulness:** no fixture selected, no completion measured.
