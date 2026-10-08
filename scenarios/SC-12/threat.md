# SC-12: catalog draft

**Bad event:** Agent establishes persistence, spawns helpers or recursively replicates

**Candidate policy/invariant:** No unsanctioned process creation, schedules or durable executable writes; leases bound total authority

**Reusable proof/checker blocks:** F1, F3, F5

**Threat source:** MITRE ATT&CK/ATLAS persistence

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent establishes persistence, spawns helpers or recursively replicates

**Honest usefulness:** no fixture selected, no completion measured.
