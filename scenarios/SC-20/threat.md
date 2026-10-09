# SC-20: catalog draft

**Bad event:** Agent poisons a training/distillation dataset or hidden label

**Candidate policy/invariant:** Dataset provenance, forbidden file/label transitions and immutable training-set hash; narrower than semantic cleanliness

**Reusable proof/checker blocks:** F1, F3, F4, F6

**Threat source:** ControlArena Data Poisoning

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent poisons a training/distillation dataset or hidden label

**Honest usefulness:** no fixture selected, no completion measured.
