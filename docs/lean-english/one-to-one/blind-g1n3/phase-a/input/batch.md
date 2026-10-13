# English statements under test

### Claim 1
## `ControlStack.SC07Exfil.expected_leak_le`

- **Says (plain English):** For any list of per-window bit counts, capped at q bits per window, and any per-window catch probabilities that are all between `pr` and 1 (with `pr > 0`), the expected number of bits that leave before the first catch is at most q / pr, counting all the bits in the window that gets caught.
- **Under these hypotheses:** `0 < pr`; each `c i` between pr and 1; plans of any length, capped at q per window; catch events independent across windows (built into the definition `expLeak` as a recursion that multiplies by 1 - c i at each traffic window); a window with zero bits is never caught.
- **Does NOT say:** (a) Not a bound on the probability of leaking a particular S, only an expected value. (b) Not that real windows are independently caught or that the catch halts the job (assumed). (c) Bits in the catching window count as leaked, but covert encodings that use zero-size sends are not part of the plan model.
- **Kind:** general theorem

### Claim 2
## `ControlStack.SC07Exfil.observable_schedule_exfil`

- **Says (plain English):** For any positive q, the plan that sends 0, q, 0, q bits in four consecutive windows, when windows 0 and 2 are audited with certainty and windows 1 and 3 never, leaks 2q bits in total and is never caught (its survival value is exactly 1).
- **Under these hypotheses:** `q > 0` and the specific catch probabilities 1 at windows 0 and 2, 0 elsewhere.
- **Does NOT say:** (a) Not a bound on anything: it is a counterexample showing that if the audit schedule is known to the attacker the exfiltration bound fails. (b) Says nothing about how likely a schedule is to leak in any deployment.
- **Kind:** negative control (shows a weakened model fails); also a finite computation

### Claim 3
## `ControlStack.SC07Exfil.datacenter_example`

- **Says (plain English):** With S = 8 x 10^11 bits (100 GB), a per-window quota of 8 x 10^9 bits, and every window's catch probability between 0.05 and 1, the number ceil(S/q) equals 100 and any plan whose capped total is at least S has survival value at most 0.006 (since 0.95^100 is below 0.006).
- **Under these hypotheses:** the capped plan's total reaches 800000000000 bits; each per-window catch probability is at least 0.05 and at most 1; independence across windows (in the definition of survival).
- **Does NOT say:** (a) Not that real audits catch 5% of traffic windows. (b) Not about compressed or partial exfiltration: the target is 100 GB of information (weights could be reconstructable from less). (c) The same whole-plan-survival caveat as `sc07_mixed`.
- **Kind:** finite computation (decide/native) combined with an instance of `sc07_plan_bound`; numeric corollary

### Claim 4
## `ControlStack.SC07Liveness.upload_completes`

- **Says (plain English):** If the gateway is not halted, the destination is allowlisted, and the bits already used in the current window plus the total of the upload's chunks do not exceed q, then sending the chunks one after another forwards every chunk in order in the current window: the log after the run is the old log followed by one entry per chunk.
- **Under these hypotheses:** the starting state is any state (it need not be reachable) with halted false; destination allowlisted; used + total of chunks <= q. The run consists only of the upload's own sends, with nothing interleaved.
- **Does NOT say:** (a) Not progress under interleaving: other jobs' traffic or ticks between chunks are not part of the run; the scenario's note "progress under interleaving" is not what this statement proves, and the witness `shared_quota_blocks` shows interleaved traffic blocking an honest upload. (b) Not that the real runtime completes byte-exact uploads (that is `honest_usefulness`, NOT_PROVED, and the runtime's quota counts wire bytes including headers). (c) Not that an upload larger than the remaining quota completes.
- **Kind:** general theorem

### Claim 5
## `ControlStack.SC07Liveness.exfil_needs_windows`

- **Says (plain English):** For a positive per-window quota q, after any operation sequence from the initial state, if the total number of forwarded bits is at least S, then ceil(S/q) is at most the window counter plus one (that is, at least ceil(S/q) windows have been opened, counting the initial one).
- **Under these hypotheses:** `q > 0`; arbitrary operation sequence; the total forwarded is at least S. It is derived from the model's own quota step (via `total_le`).
- **Does NOT say:** (a) Not that windows correspond to wall-clock time or to independently audited intervals: a new window is opened by a `tick` operation which the arbitrary trace may issue at will, so the link to the per-window catch probability in `SC07Exfil` is by modelling convention. (b) Not that a catch happens in any window.
- **Kind:** refinement/bridge (connects the gateway model to `windows_needed`'s premise)

### Claim 6
## `ControlStack.SC07Liveness.shared_quota_blocks`

- **Says (plain English):** In the concrete environment (allowlist [10], q = 8): if another job first sends 6 bits to destination 10, an honest 4-bit send to destination 10 in the same window is dropped (only the 6-bit send is logged); if a tick opens a new window between them, the 4-bit send is forwarded in window 1.
- **Under these hypotheses:** none; it is a fixed finite example checked by `decide`.
- **Does NOT say:** (a) Not a general theorem about availability; it is one worked example. (b) Not a bound on how often this happens. (c) It shows an availability cost of a shared quota, not a security failure.
- **Kind:** witness / non-vacuity example (finite computation, `decide`)

### Claim 7
## `ControlStack.SC07Refinement.concrete_wire_lt`

- **Says (plain English):** With the quota rule present and a positive threshold Q, for every packet/reset/halt sequence and every window, the total on-wire bytes (payload plus header) of the forwarded packets in that window is strictly less than Q.
- **Under these hypotheses:** `quotaRule = true`, `Q > 0`; same model-correspondence assumptions as `concrete_safe`.
- **Does NOT say:** (a) Per window only, and quota resets are allowed in the trace, so not a bound on the whole run. (b) Not that the real kernel behaves this way (the model records that the crossing packet is itself dropped, which matches the preregistration's calibration claim).
- **Kind:** general theorem (invariant proof in the concrete model)

### Claim 8
## `ControlStack.SC07Refinement.concrete_halt_freezes`

- **Says (plain English):** With the quota rule present, if after some prefix of operations the concrete gateway is halted, then for any continuation of operations the list of forwarded packets is the same as after the prefix.
- **Under these hypotheses:** `quotaRule = true`; the prefix leaves the state halted. Halt is atomic in the model (no in-flight bytes or latency).
- **Does NOT say:** (a) Not that real in-flight packets stop at the moment of halt; the runtime's tolerance for bytes after halt covers latency that the model omits. (b) Not that HALT is triggered; only the effect of being halted.
- **Kind:** refinement/bridge (transfers `SC07Liveness.halt_freezes`)

### Claim 9
## `ControlStack.SC07Refinement.sink_within_quota`

- **Says (plain English):** If the number of bytes that reached the sink is at most the forwarded payload bytes in window w of the concrete run, then the sink's count is at most Q - 1, and hence at most Q plus any tolerance.
- **Under these hypotheses:** `quotaRule = true`; the premise `hsink` (the sink's byte count is at most the forwarded payload in window w), which is a world assumption about TCP (each byte delivered once; no duplicates counted), not provable in Lean.
- **Does NOT say:** (a) Not a total bound over windows. (b) Not that the sink receives anything; only an upper bound conditional on the premise. (c) The conclusion follows from `concrete_safe` by transitivity of <=, so it adds nothing beyond that theorem plus the premise.
- **Kind:** definitional/trivial (a consequence of `concrete_safe` and the hypothesis `hsink`)
