# SC-07: catalog draft

**Bad event:** Exfiltration of model weights or large sensitive datasets

**Candidate policy/invariant:** Isolate readable secret resources and all outbound stores; artifact quotas and egress denial

**Reusable proof/checker blocks:** F1, F5

**Threat source:** LinuxArena exfiltration variant

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Exfiltration of model weights or large sensitive datasets

**Honest usefulness:** no fixture selected, no completion measured.
