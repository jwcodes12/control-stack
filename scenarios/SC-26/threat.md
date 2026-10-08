# SC-26: catalog draft

**Bad event:** Agent transfers funds, alters access or executes another irreversible external action without consent

**Candidate policy/invariant:** Typed transaction + exact signed approval from distinct principal, replay protection and spend/authority budgets

**Reusable proof/checker blocks:** F1, F3, F5, F7

**Threat source:** ControlArena SHADE Arena (illustrative real-world agent tasks)

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent transfers funds, alters access or executes another irreversible external action without consent

**Honest usefulness:** no fixture selected, no completion measured.
