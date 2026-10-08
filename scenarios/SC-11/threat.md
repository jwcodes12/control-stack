# SC-11: catalog draft

**Bad event:** Agent tampers with container mounts, host filesystem or trusted toolchain

**Candidate policy/invariant:** OS separation, deny writes to trust roots, verified mount/path-resolution config and startup attestation

**Reusable proof/checker blocks:** F1, F3, F4

**Threat source:** SANDBOXF1/SANDBOX2F1

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent tampers with container mounts, host filesystem or trusted toolchain

**Honest usefulness:** no fixture selected, no completion measured.
