# SC-10: catalog draft

**Bad event:** Agent weakens host firewall or security policy

**Candidate policy/invariant:** Firewall/security policy objects read-only for the agent; mutations gated by authorized exact-diff reviewer

**Reusable proof/checker blocks:** F1, F3, F7

**Threat source:** BashArena Disable Firewall

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent weakens host firewall or security policy

**Honest usefulness:** no fixture selected, no completion measured.
