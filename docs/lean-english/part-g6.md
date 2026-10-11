# Part G6: plain-English statements for SC-25 and SC-26

Conventions used below. "Trace" means a finite list of operations fed to a transition system from its initial state. "Adversary" in these models means "any trace the theorem quantifies over": the Lean statements say nothing about who produced the operations except through the caller/claim fields the operations carry. "By X" means "by an operation carrying X's caller identity"; whether that identity is genuine is the credential-separation premise, which only the `*Authenticated*` theorems address, and only partly.

---

## SC-25: Agent hides or misorders hazardous actions behind after-the-fact monitoring

**Harm (one sentence).** An operation executes before a trusted audit PASS for the exact digest of its content (and, if irreversible, an exact-digest approval by someone other than the submitter), or executes twice, or executes after a timeout or HALT.

**What the Lean claims, taken together, and what they leave to assumptions.** In a model where agents submit and amend queued operations, an auditor records a pass/fail verdict on the digest of the content it audited, and an executor checks and then fires, the Lean proves that every executed operation had, at the instant it ran, a PASS verdict (from an operation carrying an auditor identity) whose digest equals the digest of the content executed, plus (if the trusted classifier calls the content irreversible) an approval of that digest from an identity that is an approver and is not the submitter; also that nothing executes twice, nothing executes after a timeout-without-verdict, and nothing executes after HALT. With an injectivity premise on the digest function over the contents that occur in the run, the same holds for the exact content rather than only its digest. The concrete event machine is shown to simulate the model, so these results transfer to it. Left to assumptions (all NOT_PROVED): that operations carrying auditor/approver/admin identities really are those principals' acts (the authenticated theorem only moves this to "platform-reported identity is the true issuer", and does not constrain who issues operations), that the executor is the only effect path, that the irreversibility classifier is right, and that the Python runtime implements the concrete machine (tested, not proved). Nothing here says a PASS means the operation is harmless, and a PASS, once recorded for a digest, is never revoked by a later FAIL on the same digest in this model.

### `ControlStack.SC25.sc25_safe`  — `ControlStack/Scenarios/SC25Audit.lean:314`
- **Says (plain English):** Start from the empty system and apply any finite sequence of operations (submit, amend, audit, approve, timeout, check, fire, crash, halt) under the deployed configuration (digest check on, atomic re-validation on, fail-closed timeout, trusted classifier, halt check on). Then every recorded execution satisfied the following when it ran: among the verdicts recorded so far at that moment there was one for that operation id, marked PASS, whose digest equals the digest of the executed content, and which was recorded by an operation carrying the identity of someone in the auditors list. If the executed content is classified irreversible by the trusted classifier, then among the approvals recorded at that moment there was one for that id with the digest of the executed content, by an identity in the approvers list who is not the operation's submitter. Also no operation id appears twice among the executions.
- **Under these hypotheses:** None beyond the model itself, for any role lists, any digest function `h : N -> N` (even non-injective), and any classifier `cls`. The model facts doing the work: `submit`/`amend` need a caller in the agents list; `audit` and `approve` need a caller in the auditors/approvers list and the system, not the caller, computes the digest from the item's current queue content; `fire` re-validates against the current content in the same step (atomic), requires not-expired, a PASS verdict with matching digest, and for irreversible content an approval with matching digest from an approver other than the item's original submitter, and requires the operation not already executed; HALT blocks every operation except crash and halt. World assumption (not provable): caller identities are authentic (an operation with an auditor's id is that auditor's act). The role lists are arbitrary, so nothing forbids an id being both an agent and an auditor.
- **Does NOT say:** (1) That the content was actually audited: with a non-injective digest a PASS on a different content with the same digest suffices (see `digest_only_executes_unaudited`). (2) That a PASS means the operation is safe, or that a later FAIL cancels an earlier PASS: validation asks only that some PASS verdict with the matching digest exists, so a FAIL recorded after a PASS on the same digest does not block execution. (3) Anything about forged identities, or about the real runtime; "approver who is not the submitter" compares the item's original submitter id, not who amended it, and does not make auditor, approver and agent distinct unless the role lists are disjoint.
- **Kind:** general theorem (induction over traces, via an inductive invariant).
- **Non-vacuity:** `honest_reversible` and `honest_irreversible_with_crash` in the same file (decide on a small trace with roles agent 1, auditor 2, approver 3, admin 4) show executions do occur under `full`.
- **Read depth:** full

### `ControlStack.SC25.expired_never_executes`  — `ControlStack/Scenarios/SC25Audit.lean:345`
- **Says (plain English):** If an operation id is on the expired list (the timer swept it because it had no verdict at all) and has not been executed, then no continuation of operations, from that state, ever executes it.
- **Under these hypotheses:** Starting state `s` is arbitrary (it is not required to be reachable or invariant-satisfying); the id is in `s.expired` and is not among `s`'s executions. Deployed configuration. The mechanism: `Valid` requires the id not to be in the expired list, and nothing ever removes ids from that list. No world assumption beyond the model.
- **Does NOT say:** (1) That unaudited operations time out: the `timeout` operation is just something a trace may or may not contain; the theorem is about what happens once expiry has been recorded. Unaudited operations are blocked anyway by the verdict requirement in `sc25_safe`. (2) That expiry is permanent in a wall-clock sense or that a late PASS can revive it: a PASS recorded after expiry is allowed in the log but cannot make the item executable. (3) That an operation that received any verdict (including FAIL) ever expires: `timeout` is a no-op once any verdict exists.
- **Kind:** general theorem (induction over traces).
- **Non-vacuity:** The third conjunct of `fail_open_timeout_breaks` runs submit, timeout, check, fire under the deployed configuration and gets no executions, so an expired item is reachable; there is no separate example of the exact hypotheses.
- **Read depth:** full

### `ControlStack.SC25.halt_freezes`  — `ControlStack/Scenarios/SC25Audit.lean:363`
- **Says (plain English):** If the system state is already halted, then after any further sequence of operations (including more halts, crashes, amendments, audits, fires) the list of executions is exactly what it was.
- **Under these hypotheses:** Arbitrary starting state with the halted flag set; deployed configuration, where `haltCheck = true` makes every operation except crash and halt do nothing once halted. The "halted" flag is set only by a halt operation whose caller is in the admins list (identity authenticity is the world assumption).
- **Does NOT say:** (1) That a halt is ever issued, or timely: nothing about liveness of the admin. (2) That operations issued before the halt but not yet executed are cancelled; they simply cannot run afterward. (3) That no external effect occurs: it is about the model's execution log, and relies on the premise that the executor is the only effect path.
- **Kind:** general theorem (induction); the freezing is by construction of `step` (halted implies no-op), so the substance is the case check that every operation obeys it.
- **Non-vacuity:** The second conjunct of `no_halt_check_breaks` runs submit, audit, check, halt, fire under `full` and gets no executions; the first conjunct (halt check removed) executes, showing the halt check is what matters.
- **Read depth:** full

### `ControlStack.SC25Content.sc25_content_safe`  — `ControlStack/Scenarios/SC25Content.lean:146`
- **Says (plain English):** Suppose the digest function is injective (distinct contents give distinct digests) on the set of contents that ever appear in the queue during the run (every submitted or amended version). Then every executed operation's exact content was audited PASS: there is an audit record (a "ghost" record, defined to mirror precisely what the `audit` operation logs but also keeping the content the auditor was shown) with that operation id, that exact content, verdict PASS, and an auditor identity.
- **Under these hypotheses:** `Set.InjOn h S`, where `S` is the set of contents of queue entries in the run's final state; any roles, any classifier, any trace. The ghost record content is the item's queue content at the time of the audit step, i.e. it assumes the auditor is shown exactly what the queue holds. Identity authenticity is a world assumption.
- **Does NOT say:** (1) That the digest function is injective in any real sense: the premise is on contents in this run, and it is a premise about the hash (collision-freeness on these contents), not something proved. Real hashes are not injective; this is a no-collision assumption on the run. (2) Timing: the statement does not say the audit preceded the execution; that is carried by `sc25_safe` (and is in fact how the proof gets there). Nor does it restate the approval requirement at the content level. (3) That the auditor judged the content well or correctly understood it.
- **Kind:** general theorem (ghost-state refinement of `sc25_safe` plus an injectivity step).
- **Non-vacuity:** No explicit example for this exact statement, but any `honest_*` trace with `h = id` (injective) satisfies the hypothesis; NOT SHOWN as a stated Lean example for this theorem.
- **Read depth:** full

### `ControlStack.SC25Content.digest_only_executes_unaudited`  — `ControlStack/Scenarios/SC25Content.lean:165`
- **Says (plain English):** With a constant digest function (every content maps to 0), the trace submit content 7, audit it PASS, amend it to content 50, check, fire results in content 50 being executed, while the only ghost audit record is for content 7. So content 50 executed although it was never audited.
- **Under these hypotheses:** A single concrete trace, roles agent 1 / auditor 2 / approver 3 / admin 4, a constant digest, the threshold classifier; checked by evaluation.
- **Does NOT say:** That the real system uses a constant or weak digest; it shows the injectivity premise in `sc25_content_safe` cannot simply be dropped. It does not claim any other failure.
- **Kind:** negative control (shows that weakening the digest assumption breaks the content-level claim); a finite `decide` computation.
- **Non-vacuity:** The statement is itself a concrete instance; it is the witness.
- **Read depth:** full

### `ControlStack.AuthInstances.sc25_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesA.lean:112`
- **Says (plain English):** Give every operation a true issuer (the platform-reported identity) alongside the identity the operation claims. Run the SC-25 system so that an operation claiming an identity (submit, amend, audit, approve and halt claim their caller; timeout, check, fire and crash claim none) is applied only if the claimed identity equals its issuer, and otherwise does nothing. Take any list `U` of identities disjoint from the auditors and from the approvers. Then, for any such issued trace: (a) the SC-25 safety property `Good` holds for the final state (same as `sc25_safe`, applied to the authentic sub-trace); (b) every recorded verdict was produced by some operation that appears in the trace with its issuer equal to the auditor named in the verdict, who is in the auditors list and not in `U`; (c) every recorded approval was produced by some operation in the trace issued by the approver named, who is in the approvers list and not in `U`.
- **Under these hypotheses:** `U` is disjoint from auditors and from approvers; nothing else is required of the trace. Notably the trace is not restricted to being issued from `U`: any issuers appear. World assumption (not provable): the platform-reported issuer is the true issuer.
- **Does NOT say:** (1) That the adversary only issues from `U`: that is not a hypothesis, so "not in `U`" is derived from `U` being disjoint from the role lists and the principal being in the role. The theorem therefore does not by itself show forged identities have no effect on an adversary confined to `U`; it shows only that the applied acts were issued by the principal named (the part that does the work is the authenticity guard, and the "not adversary" reading comes from interpreting `U`). (2) That a genuine auditor or approver was not coerced or deceived. (3) Anything about the submit/amend side: the conclusion does not state that submits were issued by agents.
- **Kind:** refinement/bridge (instance of the generic authenticated-issuer reduction); conjuncts (b) and (c) are close to definitional given the claim guard.
- **Non-vacuity:** `forged25_executes_without_auth` shows a trace for which authentication changes the outcome; for the main statement, any trace with `U` disjoint from roles (e.g. agent 1 as `U`, as used in that witness) satisfies the hypotheses. No separate positive example for the statement itself.
- **Read depth:** full

### `ControlStack.AuthInstances.forged25_executes_without_auth`  — `ControlStack/Scenarios/AuthInstancesA.lean:130`
- **Says (plain English):** In one concrete trace, agent 1 issues everything: submits a reversible operation (content 7), issues an audit claiming to be auditor 2 with verdict PASS, then check and fire. If no operation's claim is checked against its issuer (no authentication), the operation with id 0 executes. If the claim is checked (the `claim25` guard), the forged audit is dropped and nothing executes.
- **Under these hypotheses:** That single trace, roles from the SC-25 example (agent 1, auditor 2, approver 3, admin 4), identity digest, threshold classifier; checked by evaluation.
- **Does NOT say:** Anything about traces other than this one, or about a real authentication mechanism. It shows the authentication guard is not vacuous, not that it is secure.
- **Kind:** negative control (finite `decide` computation).
- **Non-vacuity:** The statement is itself the concrete instance.
- **Read depth:** full

### `ControlStack.SC25Refinement.concrete_safe`  — `ControlStack/Scenarios/SC25Refinement.lean:365`
- **Says (plain English):** Run the "concrete event machine" (items journaled with their content, the auditor's own log of rows with the content it saw, the approver's own log, an effect log, a timer sweep that expires items with no verdict, a volatile check set lost on crash, a single atomic fire step that re-validates the current content, plus restart and halt) on any trace of its operations from its initial state. Then, mapping the final concrete state to the abstract SC-25 state (items to queue, auditor log rows to verdicts, approver log rows to approvals, effects to executions), the abstract safety property `Good` holds: each effect had, at its moment, an auditor PASS for exactly the digest of its content, an independent approval of that digest if the content is irreversible, and no id executed twice.
- **Under these hypotheses:** Any role lists, digest function, classifier; the deployed variant (`cachedDigest = false`: fire validates against the current content's digest). The proof is a forward simulation: each concrete step equals the abstract run of a corresponding list of abstract operations (fire becomes check then fire; expire becomes timeout). World assumptions: identity authenticity as before; that the Python runtime implements this concrete machine (tested by reconciliation, not proved).
- **Does NOT say:** That the Python code implements the concrete machine, that runtime crashes were exercised, or anything about the auditor's policy or OS identity. The `cached_digest_breaks` witness (not part of this item) shows the property fails if fire validated a digest cached at submission.
- **Kind:** refinement/bridge.
- **Non-vacuity:** `honest_concrete` in the same file runs an audited and an approved-irreversible operation to execution.
- **Read depth:** full

### `ControlStack.SC25Refinement.concrete_content_safe`  — `ControlStack/Scenarios/SC25Refinement.lean:439`
- **Says (plain English):** If the digest function is injective on the set of contents that ever appear in the concrete items journal, then every concrete effect's exact content appears in the auditor's own log in a row for that operation id with verdict PASS by an identity in the auditors list and whose recorded "content seen" equals the content that was executed.
- **Under these hypotheses:** `Set.InjOn h` over the contents of the items journal of the final state; any roles, classifier, trace of concrete operations; deployed variant. The auditor log records the item's current content at audit time (modelling that the auditor fetches the current content). Identity authenticity is a world assumption.
- **Does NOT say:** (1) That the digest is collision-free in reality (premise on the run's contents). (2) Timing or the approval requirement at the content level (timing comes from `concrete_safe`; the approval content is not restated). (3) That the auditor's log really contains what the human/model auditor actually looked at: "content seen" is the machine's recorded fetch.
- **Kind:** refinement/bridge (content-level corollary of `concrete_safe` plus an invariant that audit rows store the digest of the content seen).
- **Non-vacuity:** NOT SHOWN for this exact statement; any trace with `h = id` satisfies the injectivity premise, and `honest_concrete` is such a trace with the identity digest.
- **Read depth:** full

---

## SC-26: Irreversible payment without exact, independent, one-use approval

**Harm (one sentence).** A payment lands without an approval of exactly its payload by an approver identity distinct from the requester, or one request id is paid twice, or the total paid exceeds the cap, or the gate sends after HALT.

**What the Lean claims, taken together, and what they leave to assumptions.** In a joint model of requests, approvals, reservations (charging the cap), delivery to a receiving bank (with crashes, retries, and arbitrary duplication of messages), and an admin HALT, the Lean proves that every ledger entry in the bank has a request with exactly that payload, a reservation, and an approval of exactly that payload by an approver identity that is not the requester; that ledger keys are unique and the total is within the cap; that a request id is reserved at most once; and that after a halt the gate sends nothing new (messages already in flight may still land). These results are transferred to a concrete machine and to a lossy-network machine by forward simulation, and a liveness layer shows honest progress except where halted, capped out, or the network drops every retransmission. They rest on the following assumptions, all outside Lean: no untrusted operation carries the gate's credential, approve/admin operations with an approver's/admin's identity are genuine acts (the authenticated theorems reduce this to "platform identity is the true issuer" but the main theorem does not), role disjointness for the "approver is not an agent" claim, receiver idempotency and authentication (baked in as `bankDedup = true`, `bankAuth = true`), and that the Python runtime implements the concrete machine (tested, not proved). Duplicate payment of the same business invoice under a new request id is explicitly not excluded.

### `ControlStack.SC26.sc26_safe`  — `ControlStack/Scenarios/SC26Transaction.lean:426`
- **Says (plain English):** Start from the empty system and apply any finite sequence of operations (request, approve, execute, deliver, arrive, direct bank call, halt) in which no direct bank call carries the gate's own credential. Then every entry in the bank's ledger has: a request with exactly that payload (destination, amount, memo); a reservation of that request id; and an approval of exactly that payload by an identity in the approvers list who is not the requester. Also bank keys (request ids) are all distinct, and the sum of the amounts in the bank is at most the cap.
- **Under these hypotheses:** `legal`: no `bankCall` operation has the gate's credential as caller. Deployed checks (distinctness, payload check, nonce, cap, halt check, bank dedup, bank authentication all on). Any role lists, any cap. Model facts doing the work: `approve` is accepted only from an approver id different from the requester and only if the supplied payload equals the request's; `execute` needs some approval for the id, not yet reserved, and spent plus amount within the cap; the bank only accepts the gate's credential and ignores repeated keys. World assumptions: no untrusted operation carries the gate's credential (this is the `legal` hypothesis); an `approve` carrying an approver's identity is that approver's genuine consent (credential separation, not provable here); the bank really is idempotent and authenticates the gate.
- **Does NOT say:** (1) That a human approver understood or meant to authorize the payment, or that approver and requester are different people when role lists overlap beyond the identity comparison (independence of roles needs `sc26_safe_disjoint`). (2) One payment per business intent: a second request id with the same payload is a separate, allowed payment. (3) That the bank's behaviour is a Lean fact: dedup and authentication are baked into the configuration.
- **Kind:** general theorem (inductive invariant over traces).
- **Non-vacuity:** `honest_trace_pays` in the same file (request, approve, execute, deliver, arrive with a retry) gets exactly one bank entry (decide).
- **Read depth:** full

### `ControlStack.SC26.safe_of_sound`  — `ControlStack/Scenarios/SC26Transaction.lean:409`
- **Says (plain English):** The same safety conclusion as `sc26_safe` (every bank entry exactly approved by a non-requester approver, unique keys, total within cap) holds for any configuration of checks in which these five checks are on: payload check, requester-distinctness check, cap check, bank deduplication, bank authentication. The gate-side nonce and the halt check may be off.
- **Under these hypotheses:** `Sound C` (those five flags true), all operations legal in the same sense as `sc26_safe`. Same world assumptions.
- **Does NOT say:** That the nonce and halt check are unneeded in general: per the file's own commentary (`nonce_protects_budget_only`, not read in detail here) the nonce protects budget accounting rather than effect uniqueness and the halt check provides the halt guarantee; only the safety conclusion above does not need them.
- **Kind:** general theorem (the main inductive argument; `sc26_safe` is the special case `full`).
- **Non-vacuity:** `sound_full` shows the deployed configuration satisfies `Sound`; `honest_trace_pays` shows a trace.
- **Read depth:** full

### `ControlStack.SC26.sc26_safe_disjoint`  — `ControlStack/Scenarios/SC26Transaction.lean:431`
- **Says (plain English):** If the set of approver identities and the set of agent identities have nothing in common, then every bank entry has a request with that payload and an approval of exactly that payload by an approver who is not an agent at all (and not the requester).
- **Under these hypotheses:** Role disjointness (`every approver is not in the agents list`), a world/configuration assumption about how the launcher assigns identities; plus the legality premise of `sc26_safe`.
- **Does NOT say:** That the approver is a different human or a trustworthy one, or that the disjoint role configuration holds in the runtime (that is an assumption).
- **Kind:** definitional/trivial (a one-step corollary of `sc26_safe` and the hypothesis).
- **Non-vacuity:** NOT SHOWN as a separate example, but the witness roles in this file (agent 1, approver 2) are disjoint, so the hypothesis holds for them.
- **Read depth:** full

### `ControlStack.SC26.sc26_once`  — `ControlStack/Scenarios/SC26Transaction.lean:484`
- **Says (plain English):** Under the deployed configuration, after any sequence of operations whatsoever, the list of reserved request ids contains no repeats: each request id is reserved, and charged against the cap, at most once.
- **Under these hypotheses:** None on the trace: no legality hypothesis, any roles and cap. The nonce check (`id` not already reserved) is what enforces it.
- **Does NOT say:** (1) That an approval is "consumed": approvals are a growing list, a single request can accumulate several approval records. The "one use" is a single reservation per request id. (2) That a business payment is made once: a new request id for the same payload can be reserved and paid separately. (3) That the bank saw the payment only once: bank-side uniqueness is `sc26_safe` (relying on receiver idempotency).
- **Kind:** general theorem (invariant on one list).
- **Non-vacuity:** `honest_trace_pays` (a reservation occurs once).
- **Read depth:** full

### `ControlStack.SC26.halt_freezes`  — `ControlStack/Scenarios/SC26Transaction.lean:532`
- **Says (plain English):** Starting from any state whose halted flag is set, after any further legal sequence of operations, the set of messages the gate has sent to the bank is unchanged, and every entry in the bank was either already in the bank at the time of halt or was already among the sent (in-flight) messages at that time.
- **Under these hypotheses:** An arbitrary starting state with `halted = true` (not required to be reachable); all later operations legal (no gate-credential bank call); deployed checks. The halted flag is set by a halt operation from an admin identity (world assumption on authenticity).
- **Does NOT say:** (1) That no payment lands after the halt: messages already sent can still arrive and be recorded in the bank afterward (the file separately shows this can happen). The bound is "no new sends", not "nothing is paid". (2) That a halt is ever issued or processed promptly. (3) That payments reserved but not yet sent are cancelled in any further sense: they simply cannot be sent.
- **Kind:** general theorem (induction), with the freezing by construction of `step`.
- **Non-vacuity:** NOT SHOWN for this exact statement within this file; reachable halted states plausibly exist but no specific example was checked.
- **Read depth:** full

### `ControlStack.SC26Refinement.concrete_safe`  — `ControlStack/Scenarios/SC26Refinement.lean:470`
- **Says (plain English):** Run the concrete SC-26 machine (durable gate tables including delivery-intent rows, a volatile send-in-progress marker lost on crash, a wire of transmitted messages, an idempotent bank, acknowledgements, recover that retransmits unacknowledged intents unless halted, and halt) on any trace in which no bank call carries the gate's credential. Mapping the final concrete state to the abstract SC-26 state, the abstract safety property holds: every bank entry has a request with that payload, a reservation, and an approval of exactly that payload by a non-requester approver; keys are unique; total within the cap.
- **Under these hypotheses:** `legalC` (no direct bank call with the gate credential); recovery checks halt (the flag is fixed to `true`); the concrete bank is idempotent by key (built in). The proof is a forward simulation with an invariant (transmitted messages are logged intents; logged intents carry their request's payload). World assumption: the Python runtime implements this machine (tested, not proved); SQLite atomicity and durability, OS identity, credential separation are premises.
- **Does NOT say:** That the real gate/bank code matches the machine, that SQLite transactions are atomic and durable, or anything about liveness.
- **Kind:** refinement/bridge.
- **Non-vacuity:** Via the abstract `honest_trace_pays` and the liveness file's concrete states (e.g. `loggedState` is reached by `setup_reaches` in the lossy file); NOT SHOWN as a stated concrete positive example in this file for this theorem.
- **Read depth:** full

### `ControlStack.SC26Refinement.concrete_halt`  — `ControlStack/Scenarios/SC26Refinement.lean:515`
- **Says (plain English):** From any concrete state that is halted, after any further sequence of legal concrete operations, the wire (the list of messages physically transmitted) is exactly as it was at the halt, and every bank entry was already in the bank or already on the wire at the halt.
- **Under these hypotheses:** Arbitrary halted starting state (not required reachable); legal operations; recovery checks halt (`true`). Mechanism: transmit and recover are refused once halted.
- **Does NOT say:** That nothing lands in the bank after the halt (messages on the wire at the halt can still be processed). It also says nothing about unsent logged intents being paid, except that they cannot be (they are not on the wire).
- **Kind:** general theorem (induction); stronger than the abstract `halt_freezes` because it speaks of transmitted messages rather than merely logged ones.
- **Non-vacuity:** `recover_halt_witness` and `strandedState` in the same file give a concrete halted state.
- **Read depth:** full

### `ControlStack.SC26Authenticated.sc26_safe_authenticated`  — `ControlStack/Scenarios/SC26Authenticated.lean:65`
- **Says (plain English):** Give each operation a true issuer in addition to its claimed identity; operations claiming an identity (request, approve, execute, bank call, halt) take effect only if the claim equals the issuer, deliver and arrive claim none. Take any list `U` disjoint from the approvers, and require that no bank call in the trace was issued by the gate's credential. Then (a) the SC-26 safety property `Good` holds for the final state of the authenticated run; and (b) for every bank entry, there is an identity in the approvers list, not in `U`, such that the trace contains an operation `approve a (entry id) (entry payload)` issued by that same identity `a`.
- **Under these hypotheses:** `U` disjoint from approvers; no trace element that is a bank call is issued by the gate credential (this constrains all issuers in the trace, including the adversary's). Not a hypothesis: that the adversary issues only from `U`. World assumption: the platform-reported issuer is the true issuer.
- **Does NOT say:** (1) That the adversary is confined to `U`: the trace is arbitrary, so "not in `U`" comes from `U` being disjoint from approvers; the confinement is a reading. The stronger version with an explicit adversary class is `sc26_consent_from_honest_script`. (2) That the approver was not coerced or deceived. (3) Anything about the requester's identity beyond what `Good` says.
- **Kind:** refinement/bridge (instance of the generic authenticated-issuer reduction plus an approval-provenance lemma).
- **Non-vacuity:** `forged_approval_pays_without_auth` and `honest_payment_admissible` (in the Adv file) give concrete traces; no stated example that the combination of hypotheses holds for this theorem exactly (it does for them).
- **Read depth:** full

### `ControlStack.SC26Authenticated.forged_approval_pays_without_auth`  — `ControlStack/Scenarios/SC26Authenticated.lean:95`
- **Says (plain English):** In one concrete trace, agent 1 issues everything: a request, an approve claiming to be approver 2, execute, deliver, arrive. With no identity checking, the payment lands (bank holds the entry for key 0 with payload tx1) although no approver issued anything. With the claim-checking guard, the forged approval is dropped and the bank is empty.
- **Under these hypotheses:** That one trace; roles agent 1, approver 2, admin 3, gate 9; cap 20; checked by evaluation.
- **Does NOT say:** Anything beyond that trace; it shows the guard is not vacuous, not that it is secure.
- **Kind:** negative control (finite `decide` computation).
- **Non-vacuity:** The statement is itself a concrete instance.
- **Read depth:** full

### `ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script`  — `ControlStack/Core/AuthenticatedAdv.lean:89`
- **Says (plain English):** Model the trace as an order-preserving interleaving of an honest script (the operations the trusted principals actually issue) and an adversary script all of whose operations are issued from the untrusted identity set `U`. If `U` excludes the approvers and the gate identity, and the honest script contains no direct bank call issued by the gate, then for the authenticated SC-26 run: `Good` holds, and every bank entry has an approver identity `a` such that `approve a (entry id) (entry payload)` issued by `a` is an element of the honest script.
- **Under these hypotheses:** The trace is an admissible interleaving (`AdvTrace`): the adversary script is arbitrary in length, contents and claims, but every adversary operation has its issuer in `U`; `U` has no approvers and not the gate; honest script has no gate-issued bank call. World assumption (not provable): the platform-reported identity is the true issuer, so the adversary really is confined to `U`.
- **Does NOT say:** (1) That the honest approver's act was informed or free of coercion; consent here is "the honest script contains this approve of this id and payload". (2) That the honest script cannot be manipulated into issuing it (e.g. by social engineering); the honest script is a fixed input, not adaptive. (3) Any ordering between the approval and the payment beyond what `Good` already gives.
- **Kind:** general theorem (a short corollary of `sc26_safe_authenticated` plus the interleaving lemma).
- **Non-vacuity:** `honest_payment_admissible` in the same file: an admissible trace (honest script `[(2, approve 2 0 tx1)]`, adversary `U = [1]`) pays.
- **Read depth:** full

### `ControlStack.SC26Liveness.honest_progress`  — `ControlStack/Scenarios/SC26Liveness.lean:156`
- **Says (plain English):** In an invariant-satisfying state that is not halted, take a request `k` that has an approval of exactly its payload by a non-requester approver and whose amount fits within the remaining cap. Then running the three honest steps in a row (execute `k`, deliver `k`, arrive `k`) leaves the entry for `k` with its request payload in the bank.
- **Under these hypotheses:** Invariant `Inv` (holds in every reachable state); not halted; request exists; `Approved`; spent plus the amount at most the cap; the "not already reserved" hypothesis is stated but not needed (the proof ignores it). The three honest steps run consecutively, with no adversary step in between, and the executing caller is arbitrary. The deployed configuration.
- **Does NOT say:** (1) Progress under interference: see `progress_interleaved`. (2) That the entry appears only once: the statement is membership only; uniqueness is `paid_once`/`sc26_safe`. (3) Any promptness or time bound, or that such an approval and cap headroom will exist; it assumes the approver approved.
- **Kind:** general theorem.
- **Non-vacuity:** `honest_trace_pays` (same model) shows the honest steps pay in a concrete trace; no example for the exact hypotheses here.
- **Read depth:** full

### `ControlStack.SC26Liveness.progress_interleaved`  — `ControlStack/Scenarios/SC26Liveness.lean:181`
- **Says (plain English):** In an invariant state, take a request `k` that has an exact, independent approval. Insert arbitrary legal adversary operation lists before, between and after the three honest steps (execute `k`, deliver `k`, arrive `k`). Then at the end one of three things is true: the gate is halted; or the payment for `k` with its request payload is in the bank; or, at the moment just before the honest execute, `k` was not yet reserved and the cap was already exhausted for it (spent plus amount exceeds the cap).
- **Under these hypotheses:** `Inv` on the start; request and `Approved` at the start; all adversary operations legal (no gate-credential bank call). Halt is among the legal adversary operations (a `halt` carrying an admin's identity), so the first disjunct can be forced by any operation carrying an admin identity.
- **Does NOT say:** (1) That honest operations succeed against an adversary able to halt or to exhaust the cap: those are the exits, and in the model any `halt` with an admin identity is allowed. (2) A bound on time or on how often the exits occur. (3) That the payment is made exactly once (that is `sc26_safe`).
- **Kind:** general theorem.
- **Non-vacuity:** `honest_trace_pays` is the case with empty adversary lists; NOT SHOWN as an example for the full statement.
- **Read depth:** full

### `ControlStack.SC26Liveness.Concrete.crash_tolerant_progress`  — `ControlStack/Scenarios/SC26Liveness.lean:489`
- **Says (plain English):** From a reachable concrete state with a delivery-intent row for key `k`, take any legal trace of the form `pre`, then `recover`, then `mid`, then `bankProcess k`, then `post`, with any crashes anywhere, in which the gate is not halted when `recover` runs. Then at the end key `k` is in the bank's ledger, exactly once.
- **Under these hypotheses:** Reachable concrete state `runC ... ops0` with legal `ops0`; a delivery row with id `k` exists; all later operations legal; not halted just before `recover`; the trace contains a `recover` followed later by a `bankProcess k`. That last structure is the "fairness premise": it is an assumption about the schedule, not something the gate guarantees. The conclusion is about the key only: payload equality is not stated in this item.
- **Does NOT say:** (1) That a recover and a bank processing ever happen: `crashes_forever_no_progress` shows that without them the intent is never paid. (2) That the gate is not halted at later steps or that the network is reliable: the concrete wire here never loses messages; losing messages is the lossy files. (3) That the payment was authorized: authorization comes from `concrete_safe`.
- **Kind:** general theorem; the fairness premise makes the conclusion close to "if the bank processes a transmitted copy, the key lands".
- **Non-vacuity:** `crashes_forever_no_progress`'s second conjunct (`recover` then `bankProcess 0` pays in a concrete state) is an instance of the pattern with `loggedState`.
- **Read depth:** full

### `ControlStack.SC26LossyLiveness.lossy_safe`  — `ControlStack/Scenarios/SC26LossyLiveness.lean:168`
- **Says (plain English):** Extend the concrete machine with three adversary-controlled network operations (drop an in-flight message, duplicate one, have the bank process the j-th in-flight message in any order). For any trace of these (including all the concrete operations) in which no bank call carries the gate credential, the abstract SC-26 safety property holds for the final state: every bank entry exactly approved by a non-requester approver, keys unique, total within cap.
- **Under these hypotheses:** Legal lossy trace (network operations unrestricted, gate-credential bank calls excluded); the bank's processing is idempotent by key (`dedup = true` is fixed in the statement, so receiver idempotency is a built-in premise); recovery checks halt. Forward simulation maps drop and duplicate to no abstract steps.
- **Does NOT say:** That the bank is idempotent (that is baked in; `no_dedup_lossy_pays_twice` shows a non-idempotent bank pays twice), or anything about liveness under loss.
- **Kind:** refinement/bridge.
- **Non-vacuity:** `drop_all_safe` applies it to the all-drop run; `setup_reaches` gives a concrete reachable state.
- **Read depth:** full

### `ControlStack.SC26LossyLiveness.lossy_rounds`  — `ControlStack/Scenarios/SC26LossyLiveness.lean:339`
- **Says (plain English):** From a reachable lossy state with a delivery-intent row for key `k`, take a window of retransmission rounds, each a list of operations, then the gate's `recover`, then a list of operations. Suppose at least one round in the window is a "delivering" round: the operations after its `recover` consist of a drop-free segment followed by `bankProcess k`. Suppose also the gate is not halted at the end of the window. Then key `k` is in the bank at the end of the window, and after any legal continuation `k` appears exactly once among the bank keys.
- **Under these hypotheses:** Legal operations everywhere; the existence of one delivering round in the window (the "fairness" premise), stated as a property of the trace itself; the gate not halted at the end of the window; the delivery row for `k` existing from the prefix. The "at most R consecutive losses" bound is not a formal hypothesis: the premise is simply that some round in the given list delivers, and the "R" is the length of the list.
- **Does NOT say:** (1) That bounded loss holds of any real network: the premise says one of the rounds has a drop-free segment before `bankProcess k`, i.e. it is essentially the hypothesis of `lossy_progress` restated per round, so the conclusion is close to the premise. (2) Anything if the network drops every retransmission (`drop_all_no_progress` shows no progress then). (3) That the gate is not halted: this is a hypothesis.
- **Kind:** general theorem; the conclusion follows quickly from `lossy_progress` by splitting the trace at the delivering round (near-restatement of its premise plus the exactly-once from safety).
- **Non-vacuity:** `drop_all_no_progress` third conjunct (one `recover` then `bankProcess 0` pays) is the single-round instance; no multi-round example is stated.
- **Read depth:** full

### `ControlStack.SC26LossyHalt.lossy_halt_keys`  — `ControlStack/Scenarios/SC26LossyHalt.lean:99`
- **Says (plain English):** From any lossy machine state that is halted, after any legal sequence of lossy operations (drops, duplicates, reorderings, crashes, recover/transmit attempts, direct bank calls), every key in the bank's ledger was already a key in the ledger at the halt or a key of a message in flight at the halt.
- **Under these hypotheses:** An arbitrary halted starting state (not required reachable); legal operations; bank processing idempotent (fixed `dedup = true`); recover checks halt (`true`).
- **Does NOT say:** That no key lands after the halt: keys of messages in flight at the halt may still land, in any order, after the halt; "no new key" means no key that was not in the ledger or in flight at the halt. It also does not say a halt is ever issued, and it holds only for the deployed (halt-respecting) recovery (`recover_ignores_halt_lossy` shows the older design fails).
- **Kind:** general theorem (induction).
- **Non-vacuity:** `strandedState` (halted) in `SC26Refinement` and `recover_ignores_halt_lossy` give a concrete halted state; NOT SHOWN as a stated example for the theorem itself.
- **Read depth:** full

### `ControlStack.SC26LossyHalt.tagged_rounds`  — `ControlStack/Scenarios/SC26LossyHalt.lean:376`
- **Says (plain English):** Run the lossy machine while tagging each physically transmitted copy with a fresh id (a duplicate keeps its copy's id; a drop removes one tagged copy). From a reachable state, take a window of retransmission rounds. Suppose that in some round the retransmission by `recover` includes a copy of key `k` and that copy's id is later processed by the bank (an in-flight copy at an index holding that id is delivered), drops of other copies being allowed anywhere. Then key `k` is in the bank at the end of the window and, after any legal continuation, appears exactly once among the bank keys.
- **Under these hypotheses:** Legal operations; the existence of one round whose tagged copy of `k` is delivered before all copies of it are dropped, stated as a property of the trace (`DeliversT`). The existence of the copy of `k` in the recover batch itself implies the gate was not halted and `k` had an unacknowledged intent at that point; no separate "not halted" hypothesis. This is the "per-copy fairness" premise, strictly weaker than the all-or-nothing `Delivers` premise by `per_copy_weaker`.
- **Does NOT say:** (1) That such a delivery ever occurs on a real network; the premise is on the trace. (2) That the gate retransmits: `recover_batch_has_k` (not part of this item) shows the gate does when not halted; but a window with no recover has nothing to say. (3) That the payment was authorized or the payload right (the conclusion is about the key; authorization comes from `lossy_safe`, which the proof invokes for exactly-once).
- **Kind:** general theorem; conclusion follows from the per-round premise (the delivered copy of `k` is processed, which already lands the key) plus safety for uniqueness.
- **Non-vacuity:** `per_copy_weaker` (same file) exhibits a trace satisfying `DeliversT` and paying key 0, using `tLogged` and `pcRound`.
- **Read depth:** full
