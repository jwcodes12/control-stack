# SC-23: catalog draft

**Bad event:** Prompt-injected document/tool result causes an unauthorized tool action

**Candidate policy/invariant:** Untrusted text cannot change capabilities, trusted policies or transaction identity; authorize side effects against trusted request

**Reusable proof/checker blocks:** F1, F3, F7

**Threat source:** ControlArena AgentDojo

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Prompt-injected document/tool result causes an unauthorized tool action

**Honest usefulness:** no fixture selected, no completion measured.
