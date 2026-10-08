# SC-16: catalog draft

**Bad event:** Agent ships code or config before trusted evaluation/approval

**Candidate policy/invariant:** Every deployment artifact matches the exact reviewed hash; no side effects before gate commits

**Reusable proof/checker blocks:** F3, F4, F7

**Threat source:** Async code-sabotage settings

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent ships code or config before trusted evaluation/approval

**Honest usefulness:** no fixture selected, no completion measured.
