# SC-09: catalog draft

**Bad event:** Agent obtains privileged host access or passwordless sudo

**Candidate policy/invariant:** No reachable transition grants new privileges outside an approved identity/capability lattice

**Reusable proof/checker blocks:** F1, F3

**Threat source:** BashArena Escalate Privileges

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent obtains privileged host access or passwordless sudo

**Honest usefulness:** no fixture selected, no completion measured.
