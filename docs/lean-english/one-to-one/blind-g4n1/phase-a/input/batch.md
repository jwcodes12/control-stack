# English statements under test

### Claim 1
## `ControlStack.SC18.sc18_safe`

- **Says (plain English):** Start a serving node in its initial state (nothing requested, logging pointed at the trusted sink, sink up, clock 0, not halted) with all protections on (log-before-release, fail-closed on sink outage, configuration writes restricted to admins, watchdog, halt check). Apply any list of operations (requests, log writes, releases, sink-down/up, config writes, ticks, halts) in which every admin-issued "set the sink" operation names the trusted sink. Then for every response released: the trusted log (a list of committed request ids) contained that request's id at the moment of release; the clock at release was no more than T ticks after the clock at the most recent log acknowledgement (an acknowledgement of any request, not only this one); and no request id is released more than once.
- **Under these hypotheses:** (a) `legal`: every "set sink" operation whose caller is an admin sets the sink to the trusted one (non-admin set-sink operations are always "legal" because the gate ignores them). This is a condition on the trace, and it is the place where "admins are trusted" enters; it is not proved. (b) Modelled structure: an operation's caller identity is taken at face value (credential separation is a world assumption, not proved here); a log write for a requested id, while the sink is up, counts as an acknowledgement in the node's own view and refreshes the last-acknowledgement time, and it is appended to the trusted log only if the config names the trusted sink (so "acknowledgement means durable commit" is built in; an acknowledgement from a redirected sink would be counted by the node but not appear in the trusted log, which is why the config invariant matters); `release` is the only way a response leaves; ticks happen only through tick operations (so "T ticks" is a count of tick operations, which the model lets the trace choose freely). T, the admin list and the trusted sink id are arbitrary.
- **Does NOT say:** (1) It does not say the logged record contains or matches the response: the log holds only request ids. (2) It does not say anybody reviews the log, or that monitoring other than log-before-release is intact; it does not cover tampering after commit. (3) It says nothing about wall-clock time or availability: tick operations are chosen by the trace, and nothing here shows the node serves anyone.
- **Kind:** general theorem (induction over the trace; the invariant is proved for every step under `legal`).

### Claim 2
## `ControlStack.SC18.config_untampered`

- **Says (plain English):** Under the same starting state, deployed checks and legality hypothesis as `sc18_safe`, after any such trace the logging configuration still names the trusted sink.
- **Under these hypotheses:** `legal` (admin-issued sink changes name the trusted sink). The model's gate refuses a set-sink operation unless its claimed caller is an admin. Caller identities are taken at face value (world assumption: agents cannot hold or forge admin identity; not proved here).
- **Does NOT say:** (1) It does not say that no non-admin attempted a change, only that the final value is the trusted sink; an admin re-setting it to the trusted sink is indistinguishable. (2) Given the hypothesis, much of the conclusion is a restatement: admins are assumed to point only at the trusted sink, and the only other writers are refused; the theorem therefore establishes that the gate's admin check is sufficient, not that admins behave. (3) It says nothing about the sink itself being trustworthy or reachable.
- **Kind:** general theorem (one-line corollary of the same invariant as `sc18_safe`; close to definitional once `legal` and the admin check are granted).

### Claim 3
## `ControlStack.SC18.halt_freezes`

- **Says (plain English):** If the node is in a halted state, then no sequence of operations whatsoever (under the deployed checks) adds any response to the released list. The released list afterwards equals the released list before.
- **Under these hypotheses:** the only hypothesis is that the starting state has its halted flag set; it need not be reachable or satisfy the invariant, and no legality condition on the operations is needed. Halting happens by an admin halt operation or by the watchdog when the sink has been silent too long. Halt-check is on in `full`.
- **Does NOT say:** (1) It says nothing about other state: ticks, sink up/down and the clock keep changing, and the halt flag stays set; only the released list is frozen. (2) The halt is absorbing in this model (nothing clears it); the runtime resumes after sink recovery, so the theorem describes the base model, not the runtime. (3) It does not say a halt will happen when it should; see `silent_ticks_halt` for the watchdog.
- **Kind:** general theorem (simple induction; every operation in a halted state leaves `released` and `halted` unchanged).

### Claim 4
## `ControlStack.AuthInstances.sc18_safe_authenticated`

- **Says (plain English):** Now every operation in the trace is paired with its true issuer (an identity the platform reports, not chosen by the operation). The gate applies an operation that claims an identity (set-sink and halt claim their caller) only if the claimed identity equals the true issuer; operations that claim no identity (request, log write, release, sink down/up, tick) are always applied. Let U be the set of issuers the adversary controls, assumed to contain no admin. Suppose every operation in the trace issued by someone outside U satisfies `legal` (if its claimed caller is an admin, it sets the trusted sink). Then the same conclusion as `sc18_safe` holds for the authenticated run: every release's record was in the trusted log at release time, within T ticks of the last acknowledgement, with no duplicate release.
- **Under these hypotheses:** (a) no member of U is an admin (world assumption about who the adversary controls); (b) every operation issued by a non-adversary issuer is `legal`, which includes that genuine admins only ever point the config at the trusted sink (world assumption about admin behaviour; operations issued from U need no legality); (c) the model's mapping from operation to claimed identity (`claim18`: set-sink and halt claim their caller, all else claims none); (d) the issuer attached to each operation is the real principal (issuer authenticity; this is the residual premise that the platform's identity is the true issuer, not proved).
- **Does NOT say:** (1) It does not remove the legality assumption; it narrows it to operations issued outside U, so admins still must never point logging at an untrusted sink. (2) It does not say that the platform's identity mechanism provides the true issuer, and it does not address coerced or deceived admins. (3) Operations that claim no identity (including ticks, sink up/down, log writes and releases) are unauthenticated; the theorem treats them as arbitrary environment/adversary events.
- **Kind:** refinement/bridge (reduces to `sc18_safe` on the authenticated sub-trace via `authRun_eq`, plus a check that each applied admin set-sink satisfies `legal`).

### Claim 5
## `ControlStack.AuthInstances.forged18_redirects_without_auth`

- **Says (plain English):** A single concrete example. Agent issuer 1 sends "set the sink to 66, as admin 9". With admin list [9], trusted sink 0 and T = 5: if identity claims are not checked at all, the logging sink is redirected to 66; with the identity check, it stays at 0.
- **Under these hypotheses:** only the concrete numbers in the statement. The "without authentication" run uses a claim function that claims nothing, so every operation is applied at face value.
- **Does NOT say:** (1) It is not a general theorem; it is one trace. (2) It does not show the platform's authentication works, only that the model's check blocks a forged claim. (3) It does not show that a missing check anywhere else would be caught; it is only a negative control on this check.
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).

### Claim 6
## `ControlStack.SC18Liveness.honest_release`

- **Says (plain English):** In the base model with deployed checks, from any state that is not halted and whose sink is up, running the three operations [request i, log write i, release i] in a row leaves request i among the released ids.
- **Under these hypotheses:** the starting state is not halted and the sink is up. Nothing else is assumed: the state need not satisfy the safety invariant, and the operations are exactly those three with nothing interleaved and no tick between them.
- **Does NOT say:** (1) It does not say the record is in the trusted log at release or that the release is within T of the last acknowledgement; the file's docstring cites `sc18_safe` for that, but the statement itself only asserts release and holds even for states where the config does not name the trusted sink. (2) It says nothing when an adversary acts between the three steps (see `progress_interleaved`). (3) It says nothing about latency or throughput.
- **Kind:** general theorem (small; from the step definitions).

### Claim 7
## `ControlStack.SC18Liveness.progress_interleaved`

- **Says (plain English):** Take any starting state and any four lists of operations a0, a1, a2, a3 (arbitrary, with no legality condition) inserted around the honest steps: run a0, then request i, then a1, then log write i, then a2, then release i, then a3. At the end, at least one of three things is true: request i has been released; or the node is halted; or the sink was down at the moment just before the honest log write (after a0, the honest request and a1).
- **Under these hypotheses:** none beyond the model's definitions. The starting state and the four lists are unrestricted.
- **Does NOT say:** (1) It does not say the request is served: the adversary can always make one of the other two disjuncts true by halting or by taking the sink down before the honest log write, so this is "nothing else blocks it", not guaranteed availability. (2) It does not say the sink is up when the sink is not under adversary control; the sink-down event is an adversary operation in the model. (3) It does not say anything about timing or latency (no durations below a tick).
- **Kind:** general theorem (monotonicity of requested, acknowledged, released and halted facts across arbitrary operations).

### Claim 8
## `ControlStack.SC18Liveness.silent_ticks_halt`

- **Says (plain English):** Suppose the base-model state satisfies the watchdog invariant (if not halted, the clock is at most T past the last acknowledgement) and the number n of consecutive ticks is large enough that the last acknowledgement time plus T is below the clock plus n. Then after exactly n tick operations (nothing else), the node is halted.
- **Under these hypotheses:** the invariant "not halted implies clock is within T of last acknowledgement"; the inequality "last acknowledgement + T < clock + n"; the trace is n ticks and nothing else, so no acknowledgement can refresh the timer. Watchdog and halt checks are on in `full`.
- **Does NOT say:** (1) It does not itself say nothing is released afterwards; that is `SC18.halt_freezes`. (2) It does not say the watchdog resumes after the sink recovers: halt is absorbing here, which is the recorded mismatch with the runtime (the cost in availability is exactly this theorem). (3) The ticks are model ticks; it says nothing about how soon a real watchdog fires.
- **Kind:** general theorem.

### Claim 9
## `ControlStack.SC18Liveness.Resume.resume_safe`

- **Says (plain English):** In a variant model whose watchdog only pauses serving (a paused node releases nothing, and a successful log write clears the pause), start from the initial state and run any list of operations. Then every release's request id was in the log at release time, the release came within T ticks of the clock at the last log acknowledgement, and no request id is released twice. This is the same property as `sc18_safe`, stated for the variant.
- **Under these hypotheses:** none on the trace; admins and T arbitrary. The variant model is a separate, simplified model: it has no logging configuration at all (the log write always appends to the trusted log), so config tampering is out of the variant, and it only transfers the log-before-release and timing properties.
- **Does NOT say:** (1) It does not say the variant is a faithful model of the runtime (`concrete_safe` shows that a concrete event machine refines it, and the Python-to-machine link is only tested). (2) It does not cover config tampering (see `SC18.config_untampered` for the base model). (3) It does not say pause or resume happens at the right time, only what is released.
- **Kind:** general theorem (invariant induction); a separate model, not a theorem about the base model.

### Claim 10
## `ControlStack.SC18Liveness.Resume.resume_progress`

- **Says (plain English):** In the variant model, from any state that is not halted, whose sink is up, and in which request i is already present, the two operations [log write i, release i] in a row leave request i among the released ids, even if the node was paused before.
- **Under these hypotheses:** not halted; sink up; request i already requested. No safety invariant required. The two operations are consecutive with nothing interleaved and no ticks between them.
- **Does NOT say:** (1) It does not include the "sink restored" step: the sink being up is a hypothesis. (2) It does not say anything if the adversary interleaves operations (unlike `progress_interleaved`, which is for the base model only). (3) It does not say the clock or timing is acceptable beyond what `resume_safe` already says.
- **Kind:** general theorem (small; from step definitions: a log write clears the pause and refreshes the acknowledgement time).
