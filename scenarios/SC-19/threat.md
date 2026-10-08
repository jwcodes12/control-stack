# SC-19: catalog draft

**Bad event:** Agent damages data or causes an irreversible live production side effect

**Candidate policy/invariant:** Mutations occur only in transaction/preview gate; protected backups and restoration invariants

**Reusable proof/checker blocks:** F1, F3, F4

**Threat source:** LinuxArena live environments; synchronous vs async harms

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent damages data or causes an irreversible live production side effect

**Honest usefulness:** no fixture selected, no completion measured.
