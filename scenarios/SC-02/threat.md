# SC-02: catalog draft

**Bad event:** Sender communicates across multiple episodes to a persistent receiver

**Candidate policy/invariant:** One global information budget per secret/receiver lifetime; account for every episode, reject replays

**Reusable proof/checker blocks:** F2, F3, F8

**Threat source:** Required stress test for SC-01

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Sender communicates across multiple episodes to a persistent receiver

**Honest usefulness:** no fixture selected, no completion measured.
