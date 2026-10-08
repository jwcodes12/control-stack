# SC-08: catalog draft

**Bad event:** Unauthorized process or executable runs, including malware

**Candidate policy/invariant:** Execution restricted to predetermined signed programs and exact tool RPCs

**Reusable proof/checker blocks:** F1, F4

**Threat source:** BashArena Download Malware

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Unauthorized process or executable runs, including malware

**Honest usefulness:** no fixture selected, no completion measured.
