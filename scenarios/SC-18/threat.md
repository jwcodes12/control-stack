# SC-18: catalog draft

**Bad event:** Agent disables inference logging or monitoring in model-serving infrastructure

**Candidate policy/invariant:** Serving configuration and logging invariants hold in every deployed release; only approved artifacts are loaded

**Reusable proof/checker blocks:** F1, F3, F4

**Threat source:** ControlArena Rogue Eval / vLLM

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent disables inference logging or monitoring in model-serving infrastructure

**Honest usefulness:** no fixture selected, no completion measured.
