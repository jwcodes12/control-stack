# English statements under test

### Claim 1
## `ControlStack.AuthInstances.forged16_deploys_without_auth`

- **Says (plain English):** One fixed trace in which issuer 1 (an agent) issues everything: stage 7, a review claiming to be reviewer 2, an approval claiming to be approver 3, and the deploy. Without checking claims, the deployment of content 7 to target 5 happens; with claims checked against the issuer, nothing deploys, because the review and approval are dropped.
- **Under these hypotheses:** one concrete trace, roles `R0`, identity hash; `decide`. The "no authentication" side uses a claim function that always claims nothing.
- **Does NOT say:** that a real platform can supply an unforgeable issuer, only what the gate does if it does.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).

### Claim 2
## `ControlStack.SC16Refinement.concrete_safe`

- **Says (plain English):** The concrete admission machine has a content store keyed by digest (one entry per digest; first stager kept), a mutable tag table the agent can rewrite, a reviewer log and an approver log, a used-nonce list, a deploy log and a halt flag; the deploy step fetches the bytes by the approved digest from the store and re-hashes them. For any list of concrete operations (puts, tag moves, signed reviews and approvals, deploy requests, halts) with the deployed setting (deploy by digest, not by tag), mapping the final concrete state to the abstract SC-16 state satisfies `Good`: every deployment backed by an approval for exactly its target, content hashing to the approved digest, a reviewed and non-stager-reviewed digest, nonces distinct.
- **Under these hypotheses:** arbitrary roles and hash function and any concrete operation list. Model conditions that are not proved: signatures are modelled as "a row is in a log only if the role holder wrote it" (the caller number is believed; Ed25519 unforgeability and key custody are premises); the controller is single-threaded and each deploy is one atomic step; the Python runtime is assumed to implement this machine (tested only).
- **Does NOT say:** anything about deploy-by-tag (the machine with `byTag = true` fails, see `by_tag_breaks`); that the review was bound to the target in the conclusion (the concrete machine requires a review row for the approved digest and target, but the abstract `Good` that is transferred only mentions the digest); nothing about review competence, or that the runtime code matches the machine.
- **Kind:** refinement/bridge (forward simulation `simulation_run` plus `sc16_safe`).

### Claim 3
## `ControlStack.SC16Refinement.concrete_reviewed_content`

- **Says (plain English):** For the concrete admission path, if the hash is one-to-one on the contents that appear in the abstracted final state (deployed contents plus reviewed contents), then every deployed content equals the content in some review, by a reviewer in the reviewer list who is not that content's stager.
- **Under these hypotheses:** arbitrary roles, hash, concrete operation list, deploy by digest; injectivity of the hash on the contents in play (a world assumption passed in as a hypothesis); the same unproved model conditions as `concrete_safe` (signature unforgeability, believed caller ids, atomic single-threaded controller).
- **Does NOT say:** that reviewers are non-agents (that is the separate `concrete_safe_disjoint`, not in this block's list), that review was competent, or that the Python runtime implements the machine. (A reader may notice that the concrete store keeps one entry per digest, so the injectivity hypothesis may be unnecessary for this path; the Lean statement as written still assumes it.)
- **Kind:** refinement/bridge (transfer of `sc16_reviewed_content` through the simulation).

### Claim 4
## `ControlStack.SC17.sc17_safe`

- **Says (plain English):** From any initial grant set (live and desired both equal to it), after any sequence of proposals, amendments, approvals (by any caller), out-of-band live mutations, reconciles, applies and halts, with all four checks on, every record in the `applied` log satisfies: the live grant set recorded at that apply is accepted by the ceiling predicate; it equals the desired grant set recorded at the same apply; there is an approval for that proposal id whose diff equals the diff applied, by a reviewer in the reviewer list who is not the proposal's author. In addition the list of applied proposal ids has no repeats.
- **Under these hypotheses:** The environment (reviewer list, admin list, ceiling predicate `allowed` on whole grant sets) and the initial grants are arbitrary. The initial grants need not satisfy the ceiling; only the result of an apply is checked. Model conditions, not provable in Lean: the recorded "live" after an apply is computed by the model from the desired state (it is not an observation of a real cluster), so the equality of live and desired inside the record is true by construction; the reviewer id is believed; the gate is the only writer of desired state; drift detection sees all of the real live state.
- **Does NOT say:** that live permissions stay within the ceiling between applies (out-of-band grants made after an apply, before the next apply or reconcile, are not constrained by this statement), that the ceiling is correct, that approved diffs are wise, or that the real cluster state equals the model's live state. The statement does not say that an approval was given before the apply, only that one exists in the log at the end.
- **Kind:** general theorem (inductive invariant).

### Claim 5
## `ControlStack.SC17.reconcile_restores`

- **Says (plain English):** If the state is not halted, then performing a single reconcile step (with the deployed configuration, where drift handling is on) leaves live permissions equal to the desired permissions.
- **Under these hypotheses:** only that the starting state has `halted = false` (it can be any state); arbitrary environment. Model condition not proved: the reconciler's write succeeds and sees the whole live state; nothing about how often reconcile happens.
- **Does NOT say:** that drift is prevented or reverted in any particular time; that a reconcile occurs at all; or anything once halted (a halted state ignores `reconcile`). Note also that the model's `oob` operation does not check the halt flag, so after a halt out-of-band grants can accumulate and no reconcile will revert them; the halt theorem for SC-17 concerns only the `applied` log.
- **Kind:** general theorem (one-step; short case analysis).

### Claim 6
## `ControlStack.SC17.halt_freezes`

- **Says (plain English):** If the state is halted, then after running any list of operations the `applied` log is exactly what it was: no new applies are recorded after a halt.
- **Under these hypotheses:** starting state `halted = true`; deployed configuration; arbitrary operations and environment. The halt flag is set by `halt` from a caller in the admin list (believed identity).
- **Does NOT say:** that the whole state is frozen (unlike SC-15/SC-16 versions): out-of-band mutations still change `live` after halt, because `oob` is not guarded by the halt flag (propose, amend, approve, reconcile and apply are all no-ops once halted, but the statement itself only speaks about `applied`). It does not say desired state is unchanged beyond what follows from no applies, nor that real cluster applies stop.
- **Kind:** general theorem (induction; conclusion is about the applied log only).

### Claim 7
## `ControlStack.SC17Drift.drift_bounded`

- **Says (plain English):** In a separate small model with a fixed desired grant set, a stream of out-of-band grants, ticks of a clock and manual reconciles, where a scheduler on every tick reconciles whenever `W` ticks have elapsed since the last reconcile, and where at most `d` out-of-band grants are accepted per tick, at every state reached from the start the number of live grants that are not in the desired state is at most `d` times `W`.
- **Under these hypotheses:** `0 < W` (a theorem hypothesis); `d` and `W` arbitrary naturals; scheduler on (`true`); arbitrary operation list of `oob`, `tick`, `reconcile`. The per-tick limit `d` on out-of-band mutations is not a property of any gate: the model's `oob` step simply ignores an out-of-band grant beyond `d` in the current tick, so it is an assumption about the attacker's write rate. The scheduler and clock are trusted; ticks are operations in the trace. Grants are bare numbers; counting is over the list (duplicates count).
- **Does NOT say:** that live permissions are within the ceiling at any time between reconciles (the file's own `ceiling_exceeded_between_reconciles` shows a live grant outside desired); it bounds the *number* of extra grants, not their severity. It is a separate model from `SC17Infra` (no proposals, approvals or applies; desired never changes), so it does not combine with `sc17_safe` inside Lean. It does not hold without the rate-limit and scheduler premises (the file's witness `no_schedule_unbounded_lifetime` shows the no-scheduler case).
- **Kind:** general theorem (inductive invariant with arithmetic).

### Claim 8
## `ControlStack.SC17Drift.drift_lifetime`

- **Says (plain English):** In the same drift model with the scheduler on, every entry in the "out-of-band grants since the last reconcile" record (each with the clock time at which it was added) was added fewer than `W` ticks before the current clock reading. Together with the separate fact (`live_eq`, not in this block's list) that live equals those recorded grants plus the desired state, this means every currently live out-of-band grant is less than `W` ticks old.
- **Under these hypotheses:** `0 < W`, arbitrary `d`, desired set and operation list; scheduler on; the same attacker-rate and trusted-clock premises as `drift_bounded`. The statement is literally about the model's ghost record `drift` (a bookkeeping list that exists only to state the lifetime), not directly about the live list.
- **Does NOT say:** that a grant dies within any real-time bound unless ticks track real time and the reconciler actually runs and succeeds; nor that the grant did no harm during its lifetime. "Less than `W` ticks" is in model clock units; an adversary cannot slow the clock only if the clock is genuinely trusted.
- **Kind:** general theorem (inductive invariant, `omega` finish).

### Claim 9
## `ControlStack.AuthInstances.sc17_safe_authenticated`

- **Says (plain English):** Run the SC-17 gate with true issuers (propose, amend, approve, halt claim their caller; `oob`, `reconcile`, `apply` claim nothing). From any initial grants and any list of (issuer, operation) pairs: (1) `Good` holds as in `sc17_safe`; (2) every approval in the final state came from an operation `(c, approve c id)` actually issued by `c`, where `c` is the recorded reviewer, is in the reviewer list, and is not in the adversary set; (3) every proposal record's author is the issuer of a propose/amend operation with that author, id and diff, so "reviewer is not the author" compares two real issuers.
- **Under these hypotheses:** `U` (adversary issuer ids) has no member in the reviewer list (used by (2) only). Premise left: the issuer is the true principal. Conjunct (1) is `sc17_safe` on the filtered trace.
- **Does NOT say:** that the reviewer is not deceived or coerced; that the ceiling is right; nothing is authenticated for `oob`, `reconcile`, `apply` (they claim nothing, so anyone can issue them; the gate's own checks decide their effect).
- **Kind:** refinement/bridge.

### Claim 10
## `ControlStack.AuthInstances.forged17_applies_without_auth`

- **Says (plain English):** One fixed trace: issuer 1 proposes diff `dA` (add grant (1,1,1)) as author 1, issues an approval claiming to be reviewer 2, and requests the apply. Without claim checking, the apply goes through and live permissions become the single grant (1,1,1); with claim checking, the forged approval is dropped and the applied log is empty.
- **Under these hypotheses:** one concrete trace and environment `E0` (reviewer 2, admin 9); `decide`. The two sides compare different fields (live grants without auth, applied log with auth), which is fine here but means this is a comparison of outcomes, not of one field.
- **Does NOT say:** that issuer claims cannot be forged in a real system.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).
