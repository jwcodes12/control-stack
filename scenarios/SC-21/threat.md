# SC-21: catalog draft

**Bad event:** Agent corrupts safety evaluations or selectively suppresses failures

**Candidate policy/invariant:** Frozen evaluator and dataset hashes, trace completeness, independent score computation; no unreviewed eval code modification

**Reusable proof/checker blocks:** F3, F4, F6

**Threat source:** ControlArena Eval Sabotage

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent corrupts safety evaluations or selectively suppresses failures

**Honest usefulness:** no fixture selected, no completion measured.
