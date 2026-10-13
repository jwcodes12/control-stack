# English statements under test

### Claim 1
## `ControlStack.SC25.sc25_safe`

- **Says (plain English):** Start from the empty system and apply any finite sequence of operations (submit, amend, audit, approve, timeout, check, fire, crash, halt) under the deployed configuration (digest check on, atomic re-validation on, fail-closed timeout, trusted classifier, halt check on). Then every recorded execution satisfied the following when it ran: among the verdicts recorded so far at that moment there was one for that operation id, marked PASS, whose digest equals the digest of the executed content, and which was recorded by an operation carrying the identity of someone in the auditors list. If the executed content is classified irreversible by the trusted classifier, then among the approvals recorded at that moment there was one for that id with the digest of the executed content, by an identity in the approvers list who is not the operation's submitter. Also no operation id appears twice among the executions.
- **Under these hypotheses:** None beyond the model itself, for any role lists, any digest function `h : N -> N` (even non-injective), and any classifier `cls`. The model facts doing the work: `submit`/`amend` need a caller in the agents list; `audit` and `approve` need a caller in the auditors/approvers list and the system, not the caller, computes the digest from the item's current queue content; `fire` re-validates against the current content in the same step (atomic), requires not-expired, a PASS verdict with matching digest, and for irreversible content an approval with matching digest from an approver other than the item's original submitter, and requires the operation not already executed; HALT blocks every operation except crash and halt. World assumption (not provable): caller identities are authentic (an operation with an auditor's id is that auditor's act). The role lists are arbitrary, so nothing forbids an id being both an agent and an auditor.
- **Does NOT say:** (1) That the content was actually audited: with a non-injective digest a PASS on a different content with the same digest suffices (see `digest_only_executes_unaudited`). (2) That a PASS means the operation is safe, or that a later FAIL cancels an earlier PASS: validation asks only that some PASS verdict with the matching digest exists, so a FAIL recorded after a PASS on the same digest does not block execution. (3) Anything about forged identities, or about the real runtime; "approver who is not the submitter" compares the item's original submitter id, not who amended it, and does not make auditor, approver and agent distinct unless the role lists are disjoint.
- **Kind:** general theorem (induction over traces, via an inductive invariant).

### Claim 2
## `ControlStack.SC25.expired_never_executes`

- **Says (plain English):** If an operation id is on the expired list (the timer swept it because it had no verdict at all) and has not been executed, then no continuation of operations, from that state, ever executes it.
- **Under these hypotheses:** Starting state `s` is arbitrary (it is not required to be reachable or invariant-satisfying); the id is in `s.expired` and is not among `s`'s executions. Deployed configuration. The mechanism: `Valid` requires the id not to be in the expired list, and nothing ever removes ids from that list. No world assumption beyond the model.
- **Does NOT say:** (1) That unaudited operations time out: the `timeout` operation is just something a trace may or may not contain; the theorem is about what happens once expiry has been recorded. Unaudited operations are blocked anyway by the verdict requirement in `sc25_safe`. (2) That expiry is permanent in a wall-clock sense or that a late PASS can revive it: a PASS recorded after expiry is allowed in the log but cannot make the item executable. (3) That an operation that received any verdict (including FAIL) ever expires: `timeout` is a no-op once any verdict exists.
- **Kind:** general theorem (induction over traces).

### Claim 3
## `ControlStack.SC25.halt_freezes`

- **Says (plain English):** If the system state is already halted, then after any further sequence of operations (including more halts, crashes, amendments, audits, fires) the list of executions is exactly what it was.
- **Under these hypotheses:** Arbitrary starting state with the halted flag set; deployed configuration, where `haltCheck = true` makes every operation except crash and halt do nothing once halted. The "halted" flag is set only by a halt operation whose caller is in the admins list (identity authenticity is the world assumption).
- **Does NOT say:** (1) That a halt is ever issued, or timely: nothing about liveness of the admin. (2) That operations issued before the halt but not yet executed are cancelled; they simply cannot run afterward. (3) That no external effect occurs: it is about the model's execution log, and relies on the premise that the executor is the only effect path.
- **Kind:** general theorem (induction); the freezing is by construction of `step` (halted implies no-op), so the substance is the case check that every operation obeys it.

### Claim 4
## `ControlStack.SC25Content.sc25_content_safe`

- **Says (plain English):** Suppose the digest function is injective (distinct contents give distinct digests) on the set of contents that ever appear in the queue during the run (every submitted or amended version). Then every executed operation's exact content was audited PASS: there is an audit record (a "ghost" record, defined to mirror precisely what the `audit` operation logs but also keeping the content the auditor was shown) with that operation id, that exact content, verdict PASS, and an auditor identity.
- **Under these hypotheses:** `Set.InjOn h S`, where `S` is the set of contents of queue entries in the run's final state; any roles, any classifier, any trace. The ghost record content is the item's queue content at the time of the audit step, i.e. it assumes the auditor is shown exactly what the queue holds. Identity authenticity is a world assumption.
- **Does NOT say:** (1) That the digest function is injective in any real sense: the premise is on contents in this run, and it is a premise about the hash (collision-freeness on these contents), not something proved. Real hashes are not injective; this is a no-collision assumption on the run. (2) Timing: the statement does not say the audit preceded the execution; that is carried by `sc25_safe` (and is in fact how the proof gets there). Nor does it restate the approval requirement at the content level. (3) That the auditor judged the content well or correctly understood it.
- **Kind:** general theorem (ghost-state refinement of `sc25_safe` plus an injectivity step).

### Claim 5
## `ControlStack.SC25Content.digest_only_executes_unaudited`

- **Says (plain English):** With a constant digest function (every content maps to 0), the trace submit content 7, audit it PASS, amend it to content 50, check, fire results in content 50 being executed, while the only ghost audit record is for content 7. So content 50 executed although it was never audited.
- **Under these hypotheses:** A single concrete trace, roles agent 1 / auditor 2 / approver 3 / admin 4, a constant digest, the threshold classifier; checked by evaluation.
- **Does NOT say:** That the real system uses a constant or weak digest; it shows the injectivity premise in `sc25_content_safe` cannot simply be dropped. It does not claim any other failure.
- **Kind:** negative control (shows that weakening the digest assumption breaks the content-level claim); a finite `decide` computation.

### Claim 6
## `ControlStack.AuthInstances.sc25_safe_authenticated`

- **Says (plain English):** Give every operation a true issuer (the platform-reported identity) alongside the identity the operation claims. Run the SC-25 system so that an operation claiming an identity (submit, amend, audit, approve and halt claim their caller; timeout, check, fire and crash claim none) is applied only if the claimed identity equals its issuer, and otherwise does nothing. Take any list `U` of identities disjoint from the auditors and from the approvers. Then, for any such issued trace: (a) the SC-25 safety property `Good` holds for the final state (same as `sc25_safe`, applied to the authentic sub-trace); (b) every recorded verdict was produced by some operation that appears in the trace with its issuer equal to the auditor named in the verdict, who is in the auditors list and not in `U`; (c) every recorded approval was produced by some operation in the trace issued by the approver named, who is in the approvers list and not in `U`.
- **Under these hypotheses:** `U` is disjoint from auditors and from approvers; nothing else is required of the trace. Notably the trace is not restricted to being issued from `U`: any issuers appear. World assumption (not provable): the platform-reported issuer is the true issuer.
- **Does NOT say:** (1) That the adversary only issues from `U`: that is not a hypothesis, so "not in `U`" is derived from `U` being disjoint from the role lists and the principal being in the role. The theorem therefore does not by itself show forged identities have no effect on an adversary confined to `U`; it shows only that the applied acts were issued by the principal named (the part that does the work is the authenticity guard, and the "not adversary" reading comes from interpreting `U`). (2) That a genuine auditor or approver was not coerced or deceived. (3) Anything about the submit/amend side: the conclusion does not state that submits were issued by agents.
- **Kind:** refinement/bridge (instance of the generic authenticated-issuer reduction); conjuncts (b) and (c) are close to definitional given the claim guard.

### Claim 7
## `ControlStack.AuthInstances.forged25_executes_without_auth`

- **Says (plain English):** In one concrete trace, agent 1 issues everything: submits a reversible operation (content 7), issues an audit claiming to be auditor 2 with verdict PASS, then check and fire. If no operation's claim is checked against its issuer (no authentication), the operation with id 0 executes. If the claim is checked (the `claim25` guard), the forged audit is dropped and nothing executes.
- **Under these hypotheses:** That single trace, roles from the SC-25 example (agent 1, auditor 2, approver 3, admin 4), identity digest, threshold classifier; checked by evaluation.
- **Does NOT say:** Anything about traces other than this one, or about a real authentication mechanism. It shows the authentication guard is not vacuous, not that it is secure.
- **Kind:** negative control (finite `decide` computation).

### Claim 8
## `ControlStack.SC25Refinement.concrete_safe`

- **Says (plain English):** Run the "concrete event machine" (items journaled with their content, the auditor's own log of rows with the content it saw, the approver's own log, an effect log, a timer sweep that expires items with no verdict, a volatile check set lost on crash, a single atomic fire step that re-validates the current content, plus restart and halt) on any trace of its operations from its initial state. Then, mapping the final concrete state to the abstract SC-25 state (items to queue, auditor log rows to verdicts, approver log rows to approvals, effects to executions), the abstract safety property `Good` holds: each effect had, at its moment, an auditor PASS for exactly the digest of its content, an independent approval of that digest if the content is irreversible, and no id executed twice.
- **Under these hypotheses:** Any role lists, digest function, classifier; the deployed variant (`cachedDigest = false`: fire validates against the current content's digest). The proof is a forward simulation: each concrete step equals the abstract run of a corresponding list of abstract operations (fire becomes check then fire; expire becomes timeout). World assumptions: identity authenticity as before; that the Python runtime implements this concrete machine (tested by reconciliation, not proved).
- **Does NOT say:** That the Python code implements the concrete machine, that runtime crashes were exercised, or anything about the auditor's policy or OS identity. The `cached_digest_breaks` witness (not part of this item) shows the property fails if fire validated a digest cached at submission.
- **Kind:** refinement/bridge.

### Claim 9
## `ControlStack.SC25Refinement.concrete_content_safe`

- **Says (plain English):** If the digest function is injective on the set of contents that ever appear in the concrete items journal, then every concrete effect's exact content appears in the auditor's own log in a row for that operation id with verdict PASS by an identity in the auditors list and whose recorded "content seen" equals the content that was executed.
- **Under these hypotheses:** `Set.InjOn h` over the contents of the items journal of the final state; any roles, classifier, trace of concrete operations; deployed variant. The auditor log records the item's current content at audit time (modelling that the auditor fetches the current content). Identity authenticity is a world assumption.
- **Does NOT say:** (1) That the digest is collision-free in reality (premise on the run's contents). (2) Timing or the approval requirement at the content level (timing comes from `concrete_safe`; the approval content is not restated). (3) That the auditor's log really contains what the human/model auditor actually looked at: "content seen" is the machine's recorded fetch.
- **Kind:** refinement/bridge (content-level corollary of `concrete_safe` plus an invariant that audit rows store the digest of the content seen).

### Claim 10
## `ControlStack.SC26.sc26_safe`

- **Says (plain English):** Start from the empty system and apply any finite sequence of operations (request, approve, execute, deliver, arrive, direct bank call, halt) in which no direct bank call carries the gate's own credential. Then every entry in the bank's ledger has: a request with exactly that payload (destination, amount, memo); a reservation of that request id; and an approval of exactly that payload by an identity in the approvers list who is not the requester. Also bank keys (request ids) are all distinct, and the sum of the amounts in the bank is at most the cap.
- **Under these hypotheses:** `legal`: no `bankCall` operation has the gate's credential as caller. Deployed checks (distinctness, payload check, nonce, cap, halt check, bank dedup, bank authentication all on). Any role lists, any cap. Model facts doing the work: `approve` is accepted only from an approver id different from the requester and only if the supplied payload equals the request's; `execute` needs some approval for the id, not yet reserved, and spent plus amount within the cap; the bank only accepts the gate's credential and ignores repeated keys. World assumptions: no untrusted operation carries the gate's credential (this is the `legal` hypothesis); an `approve` carrying an approver's identity is that approver's genuine consent (credential separation, not provable here); the bank really is idempotent and authenticates the gate.
- **Does NOT say:** (1) That a human approver understood or meant to authorize the payment, or that approver and requester are different people when role lists overlap beyond the identity comparison (independence of roles needs `sc26_safe_disjoint`). (2) One payment per business intent: a second request id with the same payload is a separate, allowed payment. (3) That the bank's behaviour is a Lean fact: dedup and authentication are baked into the configuration.
- **Kind:** general theorem (inductive invariant over traces).
