# Part G4: SC-18, SC-19, SC-20 (plain-English statements)

Conventions used below. "Model" means the Lean state machine in the named file, not a running system. A "trace" is a finite list of operations applied one at a time to a state. "Deployed checks" (`full`) means every protective check in the model's `Checks` record is switched on. File paths are relative to `/var/tmp/sol-deployment-slice-20261010/`.

---

## SC-18: Agent disables inference logging or monitoring in model-serving infrastructure

**Status in input:** CONDITIONAL.

**Harm (one sentence).** A response leaves the serving node without a committed record in the trusted log, or more than T ticks after the last log acknowledgement, or the logging configuration is changed by a non-admin (where "by X" means "by an operation carrying X's claimed identity").

**What the Lean claims, taken together, and what they leave to assumptions.** In the base model, for every trace in which admin-issued sink changes point only at the trusted sink, every released response had its request id in the trusted log at release time, was released at most T ticks (tick operations) after the clock reading of the most recent log acknowledgement, and no request id is released twice; the configuration always names the trusted sink; and once halted nothing more is released. A wrapper theorem replaces "every caller identity is genuine" by "an operation claiming identity x is applied only if its true issuer is x", leaving the admin-legality premise only for operations issued outside the adversary's issuer set. Liveness theorems say an honest request is served unless the adversary halts the node or takes the sink down, and a variant model with a resumable pause is proved safe the same way; a concrete proxy/sink event machine is shown to refine that variant. What is left to assumption: credential separation and issuer authenticity, that a sink acknowledgement is a durable commit, that `release` is the only exit path, that admins never point the config elsewhere (the `legal` premise, which the base theorem takes as a hypothesis rather than proving), that the tick counter tracks real time, and (for the concrete machine) a scheduling premise `promptReply` that is built into the model's release guard. Only logging-before-release is modelled; nothing in these theorems covers monitoring in the sense of anyone reviewing the log, and the base model's absorbing halt does not match the runtime's resume behaviour (the model/runtime mismatch recorded in the scenario).

---

### `ControlStack.SC18.sc18_safe`  — `ControlStack/Scenarios/SC18Logging.lean:219`
- **Says (plain English):** Start a serving node in its initial state (nothing requested, logging pointed at the trusted sink, sink up, clock 0, not halted) with all protections on (log-before-release, fail-closed on sink outage, configuration writes restricted to admins, watchdog, halt check). Apply any list of operations (requests, log writes, releases, sink-down/up, config writes, ticks, halts) in which every admin-issued "set the sink" operation names the trusted sink. Then for every response released: the trusted log (a list of committed request ids) contained that request's id at the moment of release; the clock at release was no more than T ticks after the clock at the most recent log acknowledgement (an acknowledgement of any request, not only this one); and no request id is released more than once.
- **Under these hypotheses:** (a) `legal`: every "set sink" operation whose caller is an admin sets the sink to the trusted one (non-admin set-sink operations are always "legal" because the gate ignores them). This is a condition on the trace, and it is the place where "admins are trusted" enters; it is not proved. (b) Modelled structure: an operation's caller identity is taken at face value (credential separation is a world assumption, not proved here); a log write for a requested id, while the sink is up, counts as an acknowledgement in the node's own view and refreshes the last-acknowledgement time, and it is appended to the trusted log only if the config names the trusted sink (so "acknowledgement means durable commit" is built in; an acknowledgement from a redirected sink would be counted by the node but not appear in the trusted log, which is why the config invariant matters); `release` is the only way a response leaves; ticks happen only through tick operations (so "T ticks" is a count of tick operations, which the model lets the trace choose freely). T, the admin list and the trusted sink id are arbitrary.
- **Does NOT say:** (1) It does not say the logged record contains or matches the response: the log holds only request ids. (2) It does not say anybody reviews the log, or that monitoring other than log-before-release is intact; it does not cover tampering after commit. (3) It says nothing about wall-clock time or availability: tick operations are chosen by the trace, and nothing here shows the node serves anyone.
- **Kind:** general theorem (induction over the trace; the invariant is proved for every step under `legal`).
- **Non-vacuity:** `ControlStack.SC18.honest_logged_release` (finite `decide`): with admin 9, trusted sink 0, T = 2, the trace [request 0, logWrite 0, release 0] releases request 0 with the trusted log equal to [0].
- **Read depth:** full (read `step`, `legal`, `RelOk`, `Good`, `Inv`, `step_inv`, `run_inv`).

### `ControlStack.SC18.config_untampered`  — `ControlStack/Scenarios/SC18Logging.lean:225`
- **Says (plain English):** Under the same starting state, deployed checks and legality hypothesis as `sc18_safe`, after any such trace the logging configuration still names the trusted sink.
- **Under these hypotheses:** `legal` (admin-issued sink changes name the trusted sink). The model's gate refuses a set-sink operation unless its claimed caller is an admin. Caller identities are taken at face value (world assumption: agents cannot hold or forge admin identity; not proved here).
- **Does NOT say:** (1) It does not say that no non-admin attempted a change, only that the final value is the trusted sink; an admin re-setting it to the trusted sink is indistinguishable. (2) Given the hypothesis, much of the conclusion is a restatement: admins are assumed to point only at the trusted sink, and the only other writers are refused; the theorem therefore establishes that the gate's admin check is sufficient, not that admins behave. (3) It says nothing about the sink itself being trustworthy or reachable.
- **Kind:** general theorem (one-line corollary of the same invariant as `sc18_safe`; close to definitional once `legal` and the admin check are granted).
- **Non-vacuity:** `ControlStack.SC18.honest_logged_release` and `agent_writable_config_breaks` (the latter's second conjunct shows the `full` config keeps logging at the trusted sink against an agent set-sink attempt). No separate witness for this theorem; the hypothesis `legal` holds for any trace with no admin set-sink, e.g. the empty trace.
- **Read depth:** full.

### `ControlStack.SC18.halt_freezes`  — `ControlStack/Scenarios/SC18Logging.lean:240`
- **Says (plain English):** If the node is in a halted state, then no sequence of operations whatsoever (under the deployed checks) adds any response to the released list. The released list afterwards equals the released list before.
- **Under these hypotheses:** the only hypothesis is that the starting state has its halted flag set; it need not be reachable or satisfy the invariant, and no legality condition on the operations is needed. Halting happens by an admin halt operation or by the watchdog when the sink has been silent too long. Halt-check is on in `full`.
- **Does NOT say:** (1) It says nothing about other state: ticks, sink up/down and the clock keep changing, and the halt flag stays set; only the released list is frozen. (2) The halt is absorbing in this model (nothing clears it); the runtime resumes after sink recovery, so the theorem describes the base model, not the runtime. (3) It does not say a halt will happen when it should; see `silent_ticks_halt` for the watchdog.
- **Kind:** general theorem (simple induction; every operation in a halted state leaves `released` and `halted` unchanged).
- **Non-vacuity:** a halted state is produced by an admin `halt` operation, and `ControlStack.SC18Liveness.outage_fail_closed` (finite `decide`) exhibits `halted = true` after three silent ticks with T = 2.
- **Read depth:** full.

### `ControlStack.AuthInstances.sc18_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesB.lean:212`
- **Says (plain English):** Now every operation in the trace is paired with its true issuer (an identity the platform reports, not chosen by the operation). The gate applies an operation that claims an identity (set-sink and halt claim their caller) only if the claimed identity equals the true issuer; operations that claim no identity (request, log write, release, sink down/up, tick) are always applied. Let U be the set of issuers the adversary controls, assumed to contain no admin. Suppose every operation in the trace issued by someone outside U satisfies `legal` (if its claimed caller is an admin, it sets the trusted sink). Then the same conclusion as `sc18_safe` holds for the authenticated run: every release's record was in the trusted log at release time, within T ticks of the last acknowledgement, with no duplicate release.
- **Under these hypotheses:** (a) no member of U is an admin (world assumption about who the adversary controls); (b) every operation issued by a non-adversary issuer is `legal`, which includes that genuine admins only ever point the config at the trusted sink (world assumption about admin behaviour; operations issued from U need no legality); (c) the model's mapping from operation to claimed identity (`claim18`: set-sink and halt claim their caller, all else claims none); (d) the issuer attached to each operation is the real principal (issuer authenticity; this is the residual premise that the platform's identity is the true issuer, not proved).
- **Does NOT say:** (1) It does not remove the legality assumption; it narrows it to operations issued outside U, so admins still must never point logging at an untrusted sink. (2) It does not say that the platform's identity mechanism provides the true issuer, and it does not address coerced or deceived admins. (3) Operations that claim no identity (including ticks, sink up/down, log writes and releases) are unauthenticated; the theorem treats them as arbitrary environment/adversary events.
- **Kind:** refinement/bridge (reduces to `sc18_safe` on the authenticated sub-trace via `authRun_eq`, plus a check that each applied admin set-sink satisfies `legal`).
- **Non-vacuity:** NOT SHOWN as a named instance with a non-empty trace. The hypotheses hold trivially for the empty trace, and for honest traces with U disjoint from the admins; `forged18_redirects_without_auth` shows the setting is non-trivial.
- **Read depth:** full (read `claim18`, `authRun`, `authRun_eq`, `claim_issued_by`, `Authentic`, `applied`).

### `ControlStack.AuthInstances.forged18_redirects_without_auth`  — `ControlStack/Scenarios/AuthInstancesB.lean:228`
- **Says (plain English):** A single concrete example. Agent issuer 1 sends "set the sink to 66, as admin 9". With admin list [9], trusted sink 0 and T = 5: if identity claims are not checked at all, the logging sink is redirected to 66; with the identity check, it stays at 0.
- **Under these hypotheses:** only the concrete numbers in the statement. The "without authentication" run uses a claim function that claims nothing, so every operation is applied at face value.
- **Does NOT say:** (1) It is not a general theorem; it is one trace. (2) It does not show the platform's authentication works, only that the model's check blocks a forged claim. (3) It does not show that a missing check anywhere else would be caught; it is only a negative control on this check.
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).
- **Non-vacuity:** this is itself the concrete example; the contrast of the two runs is the content.
- **Read depth:** full.

### `ControlStack.SC18Liveness.honest_release`  — `ControlStack/Scenarios/SC18Liveness.lean:128`
- **Says (plain English):** In the base model with deployed checks, from any state that is not halted and whose sink is up, running the three operations [request i, log write i, release i] in a row leaves request i among the released ids.
- **Under these hypotheses:** the starting state is not halted and the sink is up. Nothing else is assumed: the state need not satisfy the safety invariant, and the operations are exactly those three with nothing interleaved and no tick between them.
- **Does NOT say:** (1) It does not say the record is in the trusted log at release or that the release is within T of the last acknowledgement; the file's docstring cites `sc18_safe` for that, but the statement itself only asserts release and holds even for states where the config does not name the trusted sink. (2) It says nothing when an adversary acts between the three steps (see `progress_interleaved`). (3) It says nothing about latency or throughput.
- **Kind:** general theorem (small; from the step definitions).
- **Non-vacuity:** the initial state is not halted with the sink up; `SC18.honest_logged_release` runs the same triple from `init`.
- **Read depth:** full.

### `ControlStack.SC18Liveness.progress_interleaved`  — `ControlStack/Scenarios/SC18Liveness.lean:142`
- **Says (plain English):** Take any starting state and any four lists of operations a0, a1, a2, a3 (arbitrary, with no legality condition) inserted around the honest steps: run a0, then request i, then a1, then log write i, then a2, then release i, then a3. At the end, at least one of three things is true: request i has been released; or the node is halted; or the sink was down at the moment just before the honest log write (after a0, the honest request and a1).
- **Under these hypotheses:** none beyond the model's definitions. The starting state and the four lists are unrestricted.
- **Does NOT say:** (1) It does not say the request is served: the adversary can always make one of the other two disjuncts true by halting or by taking the sink down before the honest log write, so this is "nothing else blocks it", not guaranteed availability. (2) It does not say the sink is up when the sink is not under adversary control; the sink-down event is an adversary operation in the model. (3) It does not say anything about timing or latency (no durations below a tick).
- **Kind:** general theorem (monotonicity of requested, acknowledged, released and halted facts across arbitrary operations).
- **Non-vacuity:** NOT SHOWN as a separate example; the honest triple from `init` with empty a-lists is covered by `honest_release` and `SC18.honest_logged_release`.
- **Read depth:** full.

### `ControlStack.SC18Liveness.silent_ticks_halt`  — `ControlStack/Scenarios/SC18Liveness.lean:192`
- **Says (plain English):** Suppose the base-model state satisfies the watchdog invariant (if not halted, the clock is at most T past the last acknowledgement) and the number n of consecutive ticks is large enough that the last acknowledgement time plus T is below the clock plus n. Then after exactly n tick operations (nothing else), the node is halted.
- **Under these hypotheses:** the invariant "not halted implies clock is within T of last acknowledgement"; the inequality "last acknowledgement + T < clock + n"; the trace is n ticks and nothing else, so no acknowledgement can refresh the timer. Watchdog and halt checks are on in `full`.
- **Does NOT say:** (1) It does not itself say nothing is released afterwards; that is `SC18.halt_freezes`. (2) It does not say the watchdog resumes after the sink recovers: halt is absorbing here, which is the recorded mismatch with the runtime (the cost in availability is exactly this theorem). (3) The ticks are model ticks; it says nothing about how soon a real watchdog fires.
- **Kind:** general theorem.
- **Non-vacuity:** `ControlStack.SC18Liveness.outage_fail_closed` (finite `decide`) with T = 2 shows three silent ticks halting the node.
- **Read depth:** full.

### `ControlStack.SC18Liveness.Resume.resume_safe`  — `ControlStack/Scenarios/SC18Liveness.lean:338`
- **Says (plain English):** In a variant model whose watchdog only pauses serving (a paused node releases nothing, and a successful log write clears the pause), start from the initial state and run any list of operations. Then every release's request id was in the log at release time, the release came within T ticks of the clock at the last log acknowledgement, and no request id is released twice. This is the same property as `sc18_safe`, stated for the variant.
- **Under these hypotheses:** none on the trace; admins and T arbitrary. The variant model is a separate, simplified model: it has no logging configuration at all (the log write always appends to the trusted log), so config tampering is out of the variant, and it only transfers the log-before-release and timing properties.
- **Does NOT say:** (1) It does not say the variant is a faithful model of the runtime (`concrete_safe` shows that a concrete event machine refines it, and the Python-to-machine link is only tested). (2) It does not cover config tampering (see `SC18.config_untampered` for the base model). (3) It does not say pause or resume happens at the right time, only what is released.
- **Kind:** general theorem (invariant induction); a separate model, not a theorem about the base model.
- **Non-vacuity:** `ControlStack.SC18Liveness.Resume.pause_then_resume` (finite `decide`) shows a release before the pause, a pause that blocks release and a later release after the sink returns.
- **Read depth:** full.

### `ControlStack.SC18Liveness.Resume.resume_progress`  — `ControlStack/Scenarios/SC18Liveness.lean:351`
- **Says (plain English):** In the variant model, from any state that is not halted, whose sink is up, and in which request i is already present, the two operations [log write i, release i] in a row leave request i among the released ids, even if the node was paused before.
- **Under these hypotheses:** not halted; sink up; request i already requested. No safety invariant required. The two operations are consecutive with nothing interleaved and no ticks between them.
- **Does NOT say:** (1) It does not include the "sink restored" step: the sink being up is a hypothesis. (2) It does not say anything if the adversary interleaves operations (unlike `progress_interleaved`, which is for the base model only). (3) It does not say the clock or timing is acceptable beyond what `resume_safe` already says.
- **Kind:** general theorem (small; from step definitions: a log write clears the pause and refreshes the acknowledgement time).
- **Non-vacuity:** `ControlStack.SC18Liveness.Resume.pause_then_resume` has exactly this situation (final conjunct).
- **Read depth:** full.

### `ControlStack.SC18Refinement.concrete_safe`  — `ControlStack/Scenarios/SC18Refinement.lean:327`
- **Says (plain English):** There is a concrete machine of the proxy and sink events (arrive, send, commit, ack, timeout, release, tick, ping, sink crash, sink restart) in its "real" setting (fail-open off, the `promptReply` scheduling flag on). For any T and any list of these events from the initial state: every released reply has its request id among the acknowledgements the proxy had read before replying (as seen through the abstraction into the variant model), the reply's clock is at most T past the clock of the last record acknowledgement, and no request id is replied to twice.
- **Under these hypotheses:** (a) the modelled machine's rules, including: an ack can only be read for a record already in the sink's durable (fsynced) log, so "ack means durable commit" is built in; there is a single sink and the sink's identity is not modelled; release needs that id's ack to have been read and no earlier reply; (b) in the `real` setting the release guard also requires that the reply happen within T ticks of reading that id's ack. This is the `promptReply` premise, which the real proxy does not check; the model refuses any release that would violate it, so the "within T" clause largely follows from this guard, not from the watchdog (the machine's release does not test the serving flag); (c) the abstraction: the variant model's last-ack time is the time of the last record ack, not pings; (d) no admin halts in the concrete machine (the transfer uses an empty admin list); (e) no config or tamper operations.
- **Does NOT say:** (1) It does not say the Python proxy implements this machine; the scenario's mapping marks that link as tested (`reconcile.py`), not proved. (2) It does not say that replies are prompt in reality: that is the premise `promptReply`, observed in the reference run but not enforced. (3) It does not cover config tampering, forged acks, adversarial clients, digest matching of the record to the body, latency or the single-release-path premise.
- **Kind:** refinement/bridge (forward simulation into `Resume`, then `Resume.resume_safe` transferred).
- **Non-vacuity:** `ControlStack.SC18Refinement.pause_resume_witness` (finite `decide`): the `real` machine releases requests 0 and 1 around a pause and resume; `honest_path` proves a fresh request is released.
- **Read depth:** full.

### `ControlStack.SC18Refinement.concrete_durable`  — `ControlStack/Scenarios/SC18Refinement.lean:338`
- **Says (plain English):** For the same concrete machine in its `real` setting, from the initial state and any event list, every released reply satisfies three things: its request id is among the first r.llen acknowledgements the proxy had read (r.llen being the number read when it replied); that id is in the sink's fsynced record log; and its clock is at most T past the clock of the last record acknowledgement.
- **Under these hypotheses:** same as `concrete_safe` (including the `promptReply` guard in release and the rule that an ack is read only for a record already in the sink's log). The "in the sink log" part additionally uses the concrete machine's invariant that every release was preceded by a read ack and every read ack names a logged record, which is the modelled "the sink acks only after fsync".
- **Does NOT say:** (1) It does not say that the sink's fsynced log in the real system is durable or tamper-evident; "the sink log" is the model's list. (2) It does not say that the log is the trusted log in the sense of the configuration (the concrete machine has one sink and no configuration). (3) The timing clause is not independent evidence: it follows from the model's `promptReply` guard, which is a premise.
- **Kind:** refinement/bridge (corollary of `concrete_safe` plus the concrete invariant).
- **Non-vacuity:** `pause_resume_witness` and `honest_path` (same as above).
- **Read depth:** full.

---

## SC-19: Agent damages data or causes an irreversible live production side effect

**Status in input:** CONDITIONAL.

**Harm (one sentence).** A destructive commit affects more than R objects, lacks a verified snapshot at exactly the destroyed version, lacks an approval by someone other than the author, or the same operation commits twice (with "by X" read as "by an operation carrying X's claimed identity").

**What the Lean claims, taken together, and what they leave to assumptions.** In the model, for any trace starting from the empty state, every destructive commit destroyed a target that, at the moment of commit, held at most R objects (counted at commit time), had a snapshot of the same target at exactly the version destroyed which some verifier had marked verified, and carries an approval from an approver other than the operation's author; and no operation id commits twice. Once halted the whole state is frozen. The authenticated version adds that, if the adversary's issuers hold no approver or verifier role, every approval and every verification in the final state was issued by a principal holding that role. Left to assumption: that caller identities are genuine (credential separation, reduced only to issuer authenticity), that the "verify" operation reflects a real, correct restore test (in the model a verifier simply marks a snapshot index; no restore is modelled), that every write bumps the version, that destruction happens only through the modelled commit, and that the model's object count and version are the real ones. Non-versioned side effects and restore correctness are explicitly out of scope.

---

### `ControlStack.SC19.sc19_safe`  — `ControlStack/Scenarios/SC19Prod.lean:259`
- **Says (plain English):** In the model of production targets (each with a version, bumped by every write, and a size), snapshots (a copy of a target's version and size), verifiers and approvers, take the initial empty state with all checks on (fresh-snapshot, verified-snapshot, atomic count at commit, halt check), and run any list of operations (writes, snapshots, verifies, prepares, approves, commits, halts). Then for every destructive operation in the final record: the number of objects actually affected (the target's size at commit) is at most R; the snapshot it names is a snapshot of the same target with the same version as the version destroyed, and that snapshot has been marked verified by someone in the verifier list; there is an approval for that operation by someone in the approver list other than the operation's author; and no operation id appears twice in the destroyed list.
- **Under these hypotheses:** none on the trace; the environment (approver, verifier and admin lists, R) is arbitrary. In the model: callers are identified by the identity they claim (credential separation is a world assumption, not proved here); a "verify" operation just records a snapshot index (it is the "trusted verifier" assumption that this means a real restore test passed); every write bumps the target's version (hypothesis "versioned targets" is built into `write`; unversioned writes are not representable); destruction occurs only via `commit`; "author" is the claimed caller of the prepare operation.
- **Does NOT say:** (1) It does not say a verified snapshot can in fact be restored, or that any real restore test was run: "verified" means an index that a verifier-listed caller marked. (2) It does not say that approver and author are different people or agents, only different claimed identities; with unauthenticated claims an agent could use any identity. (3) It does not cover side effects outside versioned targets, downstream consumers, or the object count being the real blast radius.
- **Kind:** general theorem (invariant induction over arbitrary traces, including concurrent writes between prepare and commit).
- **Non-vacuity:** `ControlStack.SC19.honest_destructive_change` (finite `decide`): with approver 2, verifier 3, admin 9, R = 10, the trace [write 7 5, snapshot 7, verify 3 0, prepare 1 0 7, approve 2 0, commit 0 0] commits one destruction (5 objects, version 1).
- **Read depth:** full (read `step`, `DestroyOk`, `Good`, `Inv`, `step_inv`).

### `ControlStack.SC19.halt_freezes`  — `ControlStack/Scenarios/SC19Prod.lean:273`
- **Says (plain English):** If the model state is halted, then running any list of operations under the deployed checks returns exactly the same state: nothing changes at all (no writes, snapshots, approvals or destructive commits).
- **Under these hypotheses:** the starting state has its halted flag set; no other condition (it need not be reachable). The halt check is on in `full`.
- **Does NOT say:** (1) In the model, even writes and snapshots are blocked by the halt; this is a model choice and does not say that a real halt stops writes by other writers to production. (2) It does not say the halt happens in time or that an admin who halts is genuine. (3) It says nothing about operations that happen outside the model.
- **Kind:** general theorem (simple induction; every operation is the identity on a halted state).
- **Non-vacuity:** `ControlStack.SC19.no_halt_check_breaks` (finite `decide`) runs an admin halt; the `full` run then destroys nothing.
- **Read depth:** full.

### `ControlStack.AuthInstances.sc19_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesA.lean:273`
- **Says (plain English):** Pair every operation with its true issuer; the gate applies an operation that claims an identity (verify, prepare, approve, halt each claim their caller; write, snapshot, commit claim none) only if the claimed identity is the true issuer. Suppose the adversary's issuer set U contains no approver and no verifier. Then, for any trace: (1) the `sc19_safe` conclusion holds for the authenticated run; (2) every approval recorded in the final state came from an operation in the trace whose issuer is an approver and is not in U; (3) every verified snapshot index was verified by an operation in the trace issued by a verifier not in U.
- **Under these hypotheses:** U disjoint from the approver list and from the verifier list (world assumption about what the adversary controls); the true issuer attached to each operation is the real principal (issuer authenticity, not proved here); the model's `claim19` mapping.
- **Does NOT say:** (1) Conjunct (1) does not use the hypotheses at all: it is `sc19_safe` applied to the authenticated sub-trace; the content added by authentication is conjuncts (2) and (3). (2) It does not say the approving or verifying principals are honest or careful, only that they are the listed principals and not the adversary's issuers; a genuine but deceived approver is not covered. (3) It does not say the platform really provides the true issuer, and writes, snapshots and commits are not authenticated (they claim no identity).
- **Kind:** refinement/bridge (`authRun_eq` reduction to `sc19_safe` plus the generic `issued_trusted` lemma applied to approvals and verifications).
- **Non-vacuity:** NOT SHOWN as a positive example with a non-empty authenticated trace; `forged19_destroys_without_auth` shows the setting. Hypotheses hold e.g. for E0 with U = [1].
- **Read depth:** full (read `claim19`, the two step lemmas, `issued_trusted` in `Core/AuthenticatedLog.lean`).

### `ControlStack.AuthInstances.forged19_destroys_without_auth`  — `ControlStack/Scenarios/AuthInstancesA.lean:292`
- **Says (plain English):** A single example. Author 1 issues all of: write 5 objects to target 7, snapshot it, "verify" it claiming to be verifier 3, prepare a destruction, "approve" claiming to be approver 2, and commit. With approver 2, verifier 3, admin 9 and R = 10: if claims are not checked, the destruction commits (version 1, 5 objects, snapshot 0); with claims checked, nothing is destroyed.
- **Under these hypotheses:** only the concrete numbers in the statement. The "without authentication" run uses a claim function that claims nothing.
- **Does NOT say:** (1) It is not a general theorem. (2) It does not show that authentication in a real platform works. (3) It does not isolate which forged claim mattered (both the verify and the approve are forged, and either alone is enough to block the commit).
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).
- **Non-vacuity:** the example is itself the witness for the "without authentication" half; the "with authentication" half is the contrast.
- **Read depth:** full.

---

## SC-20: Agent poisons a training/distillation dataset or hidden label

**Status in input:** CONDITIONAL.

**Harm (one sentence).** A trained example's content digest is neither registered by an allowlisted source nor promoted by a reviewer who is not its writer, or an example changes after the training manifest is frozen. The input scenario states there is no formal claim that data is clean.

**What the Lean claims, taken together, and what they leave to assumptions.** In the digest-level model, after any trace from the empty state, every example used in any training run has a digest that either equals the digest the (trusted) registry holds for that example id, or equals a digest that some listed reviewer promoted for that id; once halted the state is frozen. The authenticated version adds that, if the adversary's issuers are not reviewers, every promotion was issued by a reviewer outside the adversary's set. The Lean statement is weaker than the scenario's bad-event wording in three ways, spelled out in the blocks: it does not mention the allowlist, does not mention that the promoter differs from the writer, and does not say the trained content equals the frozen content (only that its digest is admitted; the digest function is an arbitrary function and no collision resistance is assumed in Lean). What is left to assumption: that the registry and allowlisted sources are trustworthy and semantically clean, that reviewers actually review, caller identities are genuine, digests are collision-resistant on contents in play, and training reads only through the loader.

---

### `ControlStack.SC20.sc20_safe`  — `ControlStack/Scenarios/SC20Data.lean:247`
- **Says (plain English):** Take the initial empty state with all checks on (source check, quarantine of agent-written examples, re-check of digests at training time, halt check) and any list of operations (ingest from a source, agent write, edit, promote, freeze a manifest, train, halt). Then in every training run recorded, for every (example id, content used) entry: either the environment's registry maps that example id to exactly the digest of that content, or some promotion record for that example id with exactly that digest was made by a caller who is in the reviewer list.
- **Under these hypotheses:** none on the trace; the environment (allowlist, registry function, reviewer list, admin list and the digest function h) is arbitrary. In the model: callers are identified by their claimed identities (credential separation is a world assumption, not proved here); the registry is a fixed trusted function in the environment; ingestion is an environment event (it claims no identity) and takes the source on trust; training reads only through the modelled loader; the digest function is an arbitrary function (no injectivity or collision resistance is assumed), so everything is at the digest level.
- **Does NOT say:** (1) It does not say the trained data is clean or unpoisoned, and nothing about label correctness: the registry and reviewers are trusted by premise. (2) It does not state that the example's source is on the allowlist (the gate checks that before freezing, but the conclusion `Adm` only mentions the registry entry), and it does not state that the promoting reviewer differs from the writer (the gate enforces that when promoting, but the conclusion only says the promoter is in the reviewer list). The theorem is weaker than the scenario's bad-event wording on both counts. (3) It does not say that an example is unchanged after the freeze: it only says the digest of what was used is admitted; two different contents with the same digest are not distinguished, and no statement is made that the content equals the frozen one. Also a training run may be empty, in which case the claim is vacuous for that run.
- **Kind:** general theorem (invariant induction over arbitrary traces, including edits after freeze).
- **Non-vacuity:** `ControlStack.SC20.honest_training` (finite `decide`): an example from an allowlisted source with registered digest is trained on; `reviewed_promotion`: an agent-written example promoted by a reviewer is trained on.
- **Read depth:** full (read `admitted`, `manifestOf`, `intact`, `runOf`, `Adm`, `Good`, `Inv`, `step_inv`).

### `ControlStack.SC20.halt_freezes`  — `ControlStack/Scenarios/SC20Data.lean:259`
- **Says (plain English):** If the state is halted, then any list of operations under the deployed checks returns exactly the same state: no ingestion, write, edit, promotion, freeze or training run changes anything.
- **Under these hypotheses:** the starting state is halted; no other condition (it need not be reachable). Halt check is on in `full`.
- **Does NOT say:** (1) In the model even ingestion, writes and edits are blocked by halt; that is a model choice, not a statement that real writers to the data store are stopped. (2) It does not say halting happens in time or that the admin who halts is genuine. (3) It does not say that earlier training runs were safe.
- **Kind:** general theorem (simple induction).
- **Non-vacuity:** `ControlStack.SC20.no_halt_check_breaks` (finite `decide`) has an admin halt in the trace; with the check on the later training is refused. No dedicated witness for the hypothesis alone.
- **Read depth:** full.

### `ControlStack.AuthInstances.sc20_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesB.lean:92`
- **Says (plain English):** Pair every operation with its true issuer; the gate applies an operation that claims an identity (agent write, promote, freeze, halt claim their caller; ingest, edit and train claim none) only if the claimed identity is the true issuer. Suppose the adversary's issuer set U contains no reviewer. Then for any trace: (1) the `sc20_safe` conclusion holds for the authenticated run; (2) every promotion record in the final state came from a promote operation in the trace issued by a reviewer who is not in U, for that example id and with that reviewer recorded.
- **Under these hypotheses:** U disjoint from the reviewer list (world assumption about what the adversary controls); the true issuer attached to each operation is the real principal (issuer authenticity, not proved); the model's `claim20` mapping.
- **Does NOT say:** (1) Conjunct (1) is `sc20_safe` applied to the authenticated sub-trace and does not use the hypothesis; the new content is conjunct (2). (2) It does not say the issuing reviewer reviewed the data or that reviewers are honest. (3) It inherits the weaknesses of `sc20_safe` (no allowlist, no writer-differs, no frozen-content claim in the conclusion), and ingestion and edits are unauthenticated environment/adversary events (they claim no identity), so the registry trust remains a premise.
- **Kind:** refinement/bridge (`authRun_eq` reduction to `sc20_safe` plus the generic `issued_trusted` lemma applied to promotions).
- **Non-vacuity:** NOT SHOWN as a positive example with a non-empty authenticated trace; `forged20_trains_without_auth` shows the setting. Hypotheses hold e.g. with the reviewer list [2] and U = [1].
- **Read depth:** full.

### `ControlStack.AuthInstances.forged20_trains_without_auth`  — `ControlStack/Scenarios/AuthInstancesB.lean:105`
- **Says (plain English):** A single example. Agent 1 issues all of: write an example (id 1, content 66), "promote" it claiming to be reviewer 2, "freeze" a manifest claiming to be admin 9, and train. With allowlist [50], reviewer 2, admin 9: if claims are not checked, a training run on the example (1, 66) occurs; with claims checked, no training run is recorded.
- **Under these hypotheses:** only the concrete environment of the statement (the SC-20 example environment with digest equal to content). The "without authentication" run uses a claim function that claims nothing.
- **Does NOT say:** (1) It is not a general theorem. (2) It does not isolate the promotion: with authentication both the forged promote and the forged freeze are refused, and the missing freeze alone already prevents training. (3) It does not show that a real platform authenticates identities.
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).
- **Non-vacuity:** the example is itself the witness for the "without authentication" half.
- **Read depth:** full.

---

## Summary counts (this part)

- Theorems translated: 20 (12 for SC-18, 4 for SC-19, 4 for SC-20).
- Read depth `partial`: 0.
