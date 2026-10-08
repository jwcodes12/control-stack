# SC-15: catalog draft

**Bad event:** Agent inserts a hidden functional backdoor in source code

**Candidate policy/invariant:** Enforce a narrower security-sensitive invariant: no changes to specified auth/crypto/egress surfaces without review; prove contract on restricted code

**Reusable proof/checker blocks:** F1, F3, F4, F6

**Threat source:** Apps, BigCodeBench, SWE-bench Django, LinuxArena

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent inserts a hidden functional backdoor in source code

**Honest usefulness:** no fixture selected, no completion measured.
