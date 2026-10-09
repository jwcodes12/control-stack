# SC-04: catalog draft

**Bad event:** Agent leaks via logs, telemetry, diagnostic output, error strings or process timing

**Candidate policy/invariant:** Restrict all *receiver-visible* diagnostics or include them in the certified observation space

**Reusable proof/checker blocks:** F2, F3, F8

**Threat source:** SC-01 correspondence gap

**Attacker authority, deployment scope and horizon:** not yet specified.

**Thin Lean goal (not proved):** For every modeled attacker trace and every state satisfying the candidate gate premises, the prohibited event does not occur.

**Falsifier:** a concrete trace that passes the candidate trusted gate and still triggers Agent leaks via logs, telemetry, diagnostic output, error strings or process timing

**Honest usefulness:** no fixture selected, no completion measured.
