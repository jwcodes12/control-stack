# Plain-English statements, part G3 (SC-15, SC-16, SC-17)

Paths below are relative to `/var/tmp/sol-deployment-slice-20261010`. All three scenarios share one pattern: a small
"gate" state machine (a list of records plus an `Op` type) is run on an arbitrary list of operations, and an
inductive invariant is proved. Operations carry a *claimed* caller identity as an ordinary number; the gate simply
believes it unless the "authenticated" wrapper (`Core/Authenticated.lean`) is used. Every `decide` theorem is a
check of one fixed small trace, not a general statement.

---

## SC-15: Agent inserts a hidden functional backdoor in source code

**Harm (one sentence):** a code change merges without (a) an exact-content review by someone other than its author,
(b) a passing trusted CI run on exactly that content, or (c) for changes touching sensitive paths, an exact-content
security review by a non-author. The scenario explicitly makes NO formal claim about backdoors themselves.

**What the Lean claims, taken together, and what they leave to assumptions.** The Lean model is a merge gate over
changes (content digest, touched paths, declared paths). It proves that, for every sequence of proposals, amendments,
reviews, CI runs, merges and halts, anything in the `merged` log has a matching exact-content non-author review, a
passing CI record for the same content and, if its path list hits the sensitive list, a security review; and that
admin HALT freezes the state. The authenticated variant adds that every recorded review was issued by a principal
holding a reviewer/security role, provided no adversary identity holds those roles. Everything connecting this to the
bad event is left to assumptions: that reviewers and tests actually catch backdoors (not formalised; the title's
"backdoor" is not a Lean notion at all), that the `paths` field in the model really is the trusted diff (the model lets
the operation supply it), that CI is trustworthy (CI carries no identity), that the sensitive list is complete, that
the gate is the only way to the protected branch, and that identity claims are real (reduced but not removed by the
authenticated wrapper).

**World assumptions (from the scenario):**
- `credential_separation` (NOT_PROVED): operations carrying trusted identities (reviewer, approver, admin, user) are those principals' own acts. Reduced in Lean by `sc15_safe_authenticated`; the residual premise is issuer authenticity (platform identity = true issuer). CI results carry no principal, so CI trustworthiness is a separate premise.
- `review_adequacy` (NOT_PROVED): reviews and tests are adequate to detect backdoors (semantic; not formalisable here).

### `ControlStack.SC15.sc15_safe`  — `ControlStack/Scenarios/SC15Review.lean:227`
- **Says (plain English):** Start the merge gate from its empty state and feed it any list of operations in any order (proposals, amendments by the author, reviews, CI runs, merge requests, halts), using the deployed configuration `full` in which all five checks are on. Then every change in the final `merged` log satisfies the "merge-ok" condition: there is a recorded review of that change id whose recorded content equals the merged version's content, by a reviewer who is not the change's author and who holds the role the review was filed under (security role if the review was flagged "security", ordinary reviewer role otherwise); there is a passing CI record for that change id on exactly that content; and, if any path in the merged version's `paths` list is in the environment's `sensitive` list, there is also a review flagged "security" with exact content by a non-author holding the security role.
- **Under these hypotheses:** The environment `E` (reviewer list, security-reviewer list, admin list, sensitive-path list, and a `testsPass` function from content to pass/fail) is arbitrary, and the operation list is arbitrary (any caller ids, contents, paths, declared paths). Model conditions, not provable in Lean: (1) a review record stores the content the gate has for the change at review time, which is treated as "what the reviewer saw"; (2) the `paths` field supplied in `propose`/`amend` is treated as the trusted-diff path list (the model does not tie it to the content, and the adversary chooses it; only the *author-declared* list is distrusted); (3) a CI record's verdict is `testsPass` of the content, i.e. CI is a trusted function of content; (4) the caller number on a review/halt/amend is read as the true identity of the caller; (5) the merge gate is the only way to the protected branch.
- **Does NOT say:** that merged code is free of backdoors (the docstring says so explicitly; the statement is only about which approvals exist). That reviewers or CI are competent, that sensitive-path list is complete, or that the `paths` list matches the real diff. It also does not say a change merges at most once: nothing stops a second merge request for the same change from appending it again to the log (each entry still satisfies the condition); and nothing here concerns who triggers `runCI` or `merge` (they carry no caller).
- **Kind:** general theorem (induction over the trace, via an invariant).
- **Non-vacuity:** `ControlStack.SC15.honest_merge` (by `decide`, SC15Review.lean) exhibits a reviewed, tested, non-sensitive change that does merge, so the guard is satisfiable; the `*_breaks` witnesses show each check is needed.
- **Read depth:** full (read `Env`, `Change`, `Rev`, `St`, `Op`, `Checks`, `step`, `Reviewed`, `roleOk`, `RevOk`, `MergeOk`, `Inv`, and the invariant proof).

### `ControlStack.SC15.halt_freezes`  — `ControlStack/Scenarios/SC15Review.lean:240`
- **Says (plain English):** If the gate's state has its `halted` flag set, then running any list of operations (with the deployed configuration) leaves the entire state exactly unchanged: nothing is proposed, amended, reviewed, CI'd or merged afterwards.
- **Under these hypotheses:** Only that the starting state has `halted = true` (it does not need to be reachable from the empty state), the deployed configuration `full` (halt check on), and an arbitrary environment and operation list. The flag is set by a `halt` operation whose caller is in the environment's admin list (the caller number is believed, as above).
- **Does NOT say:** that a halt happens in time, that merges that occurred before the halt are undone, or that the protected branch cannot be changed by some route outside this gate. It says nothing about who can set the flag beyond the model's `admins` check.
- **Kind:** general theorem (simple induction; proof is mostly unfolding the step function).
- **Non-vacuity:** `ControlStack.SC15.no_halt_check_breaks` (by `decide`) shows a trace in which an admin halts and a later merge is refused with the check on and accepted with it off, so halted states do arise; no witness is needed for the universally-quantified halted start state beyond that.
- **Read depth:** full.

### `ControlStack.AuthInstances.sc15_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesB.lean:48`
- **Says (plain English):** Now every operation comes with a *true issuer* (the platform-reported identity), and an operation that claims an identity (propose/amend/review/halt claim their caller) is applied only if the claim equals its issuer; operations claiming nothing (`runCI`, `merge`) always apply. Run the SC-15 gate this way from the empty state on any list of (issuer, operation) pairs. Then (1) the same merge-ok condition as `sc15_safe` holds for everything merged, and (2) every review in the final state corresponds to an operation `(c, review c id sec)` that appears in the trace, issued by `c`, where `c` is the recorded reviewer, `c` is not in the adversary set `U`, and `c` holds the reviewer role (or security role for a security review).
- **Under these hypotheses:** `U` is a list of adversary issuer ids, and the hypothesis is that no id in `U` is in the environment's reviewer list or security list. Conjunct (1) does not actually use that hypothesis (it is `sc15_safe` applied to the filtered trace); conjunct (2) does. Not provable in Lean: that the issuer recorded in the trace is the real principal behind the operation (platform identity premise), that CI results are trustworthy (unauthenticated), and everything listed under `sc15_safe`.
- **Does NOT say:** The docstring says "the change author is the issuer of the proposal", but the stated conclusion has only the two conjuncts above; nothing about proposals is in the Lean statement (it is true by the same filtering but is not stated here, unlike the SC-17 analogue). It does not say the reviewer actually read or understood the content, and does not authenticate CI or `merge` requests.
- **Kind:** refinement/bridge (a reduction to `sc15_safe` via `authRun_eq`, plus a generic "logged records were issued by a trusted principal" lemma).
- **Non-vacuity:** NOT SHOWN for the authenticated statement itself (no honest authenticated trace that merges is given in this file); the unauthenticated `honest_merge` shows the underlying gate can merge, and `forged15_merges_without_auth` only shows the filtered trace refuses a forged one.
- **Read depth:** full (read `claim15`, `sc15_review_step`, `Authentic`, `authed`, `applied`, `authRun`, `authRun_eq`, `issued_trusted`, `claim_issued_by`).

### `ControlStack.AuthInstances.forged15_merges_without_auth`  — `ControlStack/Scenarios/AuthInstancesB.lean:64`
- **Says (plain English):** One fixed trace: issuer 1 issues all four operations: propose change 0 (author 1, content 7, paths [5]), then review change 0 *claiming to be reviewer 2*, then run CI, then merge. In the test environment (reviewer 2, security reviewer 3, admin 9, sensitive path 100, content 13 fails tests), if claims are not checked at all, change 0 merges; if the claim check is on, nothing merges (the forged review is dropped, so the merge has no review).
- **Under these hypotheses:** Just this concrete trace and the concrete environment `E0`; checked by `decide`. The "no authentication" side is modelled by a claim function that always claims nothing, so every operation is applied.
- **Does NOT say:** that authentication is necessary in general, only that for this one trace its removal lets an author self-approve; nor that the claim check could not be bypassed in a real system (it presumes the issuer field is trustworthy).
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).
- **Non-vacuity:** it is itself the concrete example.
- **Read depth:** full.

---

## SC-16: Agent ships code or config before trusted evaluation/approval

**Harm (one sentence):** content is deployed that was not reviewed by a non-stager reviewer, or to a target that was not approved, or twice under one approval, or after HALT.

**What the Lean claims, taken together, and what they leave to assumptions.** A shared-state model with an append-only content store, a review log (digest, reviewer, content seen, stager), one-use approvals (nonce, digest, target) and a deploy step. For any list of operations, every recorded deployment consumed a distinct approval for exactly its target, its supplied content hashes to the approved digest, and that digest has a review by a reviewer other than that review's stager; under injectivity of the hash on the contents in play the deployed content is the reviewed content, and under extra role-disjointness hypotheses the reviewer and approver are not agents. A concrete admission machine (CAS, mutable tags, signed logs) is shown to simulate the model, so the same conclusions transfer to it. What is left to assumptions: that a role identity is the principal's own act (not modelled; only reduced to platform identity), that deploy-through-the-gate is the only route to the target, that the hash has no collisions on contents in play, that reviewers and approvers are not agents (sc16_safe alone allows an agent that is a reviewer, as long as it is not that content's stager), the signature/key custody for the concrete machine, review competence, and that the Python runtime implements the concrete machine (only tested).

**World assumptions (from the scenario):**
- `credential_separation` (NOT_PROVED): every operation carrying a trusted role's identity is that principal's own act. Reduced in Lean (`sc16_safe_authenticated`); the residual premise is issuer authenticity.
- `hash_injective` (THEOREM_VERIFIED, as a hypothesis in the theorems that need it): the hash is injective on contents in the run (collision resistance).
- `exclusive_deploy_path` (NOT_PROVED): deploy through the gate is the only route to the target.
- `honest_usefulness` (NOT_PROVED): honest deployments complete.
- `role_disjointness` (NOT_PROVED): agent and reviewer/approver identities are disjoint.
- `model_runtime_correspondence` (THEOREM_VERIFIED for concrete machine to model, TESTED for Python to concrete machine): concrete admission machine to SC16 model is proved (`SC16Refinement`); Python runtime to concrete machine is tested only.

### `ControlStack.SC16.sc16_safe`  — `ControlStack/Scenarios/SC16Deploy.lean:294`
- **Says (plain English):** From the empty state, after any sequence of staging, slot writes, reviews, approvals, deploy requests and halts (any caller ids, any contents), the deployed configuration `full` guarantees that every entry in the deployment log (a) was backed by an approval with the same nonce and the same target as the deployment, made by someone in the approver list; (b) has content whose hash equals that approval's digest; (c) the approval's digest has a recorded review which is "ok" (the review's recorded content hashes to the digest, its reviewer is in the reviewer list, and the reviewer id differs from the id of the stager of that recorded content). Also the nonces of the deployments are all distinct, so no approval was used twice.
- **Under these hypotheses:** Roles `R` (agents, reviewers, approvers, admins) and the hash function `h` are completely arbitrary (h need not be injective; role lists may overlap). The caller field of each operation is believed. Model conditions: a review records the content the gate found in the store under that digest (the store's first entry with that hash), which is treated as what the reviewer saw; the deploy content is supplied at deploy time and checked against the approved digest; the deploy call has no caller restriction.
- **Does NOT say:** that the deployed content is the content that was reviewed: only that its hash equals the digest that some review has. With a colliding hash the two can differ (see `collision_breaks`). It also says the reviewer differs from the stager of the *reviewed* content, not that the reviewer is a non-agent: a different agent can review it. The approver is only required to be in the approver list, not distinct from the stager or an agent. It does not say that the review preceded the approval, or that the target is a sensible environment.
- **Kind:** general theorem (inductive invariant over traces).
- **Non-vacuity:** `ControlStack.SC16.honest_trace_deploys` (by `decide`, roles `R0`, identity hash) deploys content 7 to target 5.
- **Read depth:** full (read `Roles`, `Review`, `Appr`, `Dep`, `St`, `Op`, `Checks`, `step`, `ReviewOk`, `DepOk`, `Inv`, `Good`).

### `ControlStack.SC16.sc16_reviewed_content`  — `ControlStack/Scenarios/SC16Deploy.lean:299`
- **Says (plain English):** If the hash function is one-to-one on the set of contents that appear in this run (the contents that were deployed, together with the contents recorded in reviews), then every deployed content is literally the content some reviewer reviewed: there is a review whose recorded content equals the deployed content, whose reviewer is in the reviewer list and differs from that content's stager.
- **Under these hypotheses:** Arbitrary roles, hash function and operation list, plus the hypothesis that the hash is injective on contents that actually appear in the run. This is a world assumption (collision resistance on the run's contents) that is a hypothesis of the theorem, not something proved; it is only required on the contents in play, not globally.
- **Does NOT say:** that the reviewer was an honest non-agent (an agent other than the stager may review), that the review was competent, or that reviewed content is harmless. Nothing is said if the hash has any collision among those contents; `collision_breaks` shows that case really can deploy unreviewed content.
- **Kind:** general theorem (corollary of `sc16_safe` plus injectivity).
- **Non-vacuity:** the injectivity hypothesis holds in `honest_trace_deploys` (identity hash is injective), so it can hold together with a deployment; the theorem itself has no named witness.
- **Read depth:** full.

### `ControlStack.SC16.halt_freezes`  — `ControlStack/Scenarios/SC16Deploy.lean:321`
- **Says (plain English):** If the state is already halted, then running any list of operations under the deployed configuration leaves the whole state unchanged, in particular the deployment log: no staging, review, approval or deployment takes effect after a halt.
- **Under these hypotheses:** Starting state has `halted = true` (any state, not necessarily reachable); arbitrary roles, hash, operations; the halt check is on (`full`). The flag is set only by a `halt` operation whose caller is in the admin list (believed identity).
- **Does NOT say:** that deployments already made are undone; that an admin halts in time; or anything about deploying by a route outside the gate.
- **Kind:** general theorem (trivial induction over the trace).
- **Non-vacuity:** `ControlStack.SC16.no_halt_check_breaks` (`decide`) exhibits a trace with a real halt followed by a refused deploy.
- **Read depth:** full.

### `ControlStack.SC16Disjoint.sc16_safe_disjoint`  — `ControlStack/Scenarios/SC16Disjoint.lean:25`
- **Says (plain English):** Add three hypotheses: no reviewer is in the agent list, no approver is in the agent list, and the hash is injective on contents in play. Then for every deployment, there is a review of exactly the deployed content by a reviewer in the reviewer list, who is not an agent and is not the content's stager, and an approval with the deployment's nonce and target made by an approver in the approver list who is not an agent.
- **Under these hypotheses:** (1) reviewers and agents are disjoint; (2) approvers and agents are disjoint; (3) injectivity of the hash on the run's contents. All three are hypotheses to the theorem (role disjointness and collision resistance are world assumptions); caller identity is believed.
- **Does NOT say:** that identities are authenticated (that is `credential_separation`), that the reviewer is independent of the agent's principal (a human with an agent key, or a coerced reviewer, is out of scope), or anything about review quality. Since "not an agent" is read straight off hypothesis (1) and (2), the non-agent conclusion is essentially a restatement of the role-disjointness hypothesis applied to the reviewer/approver that `sc16_safe` already identifies.
- **Kind:** definitional/trivial (a short corollary of `sc16_reviewed_content` and `sc16_safe`; the added "not an agent" parts are the hypotheses).
- **Non-vacuity:** NOT SHOWN as a stated example for the three hypotheses together; the roles `R0` (agent 1, reviewer 2, approver 3) satisfy (1) and (2) and the identity hash satisfies (3) in `honest_trace_deploys`, but that is not packaged as a witness for this theorem.
- **Read depth:** full.

### `ControlStack.SC16Disjoint.overlap_reviewer_is_agent`  — `ControlStack/Scenarios/SC16Disjoint.lean:46`
- **Says (plain English):** With roles where agent 2 is also a reviewer (agents 1 and 2, reviewer 2, approver 3, admin 4): staging content 7 as agent 1, reviewing it as 2, approving, and deploying leads to a deployment of content 7 to target 5, there is at least one review, and every review recorded is by an agent. So the weaker theorem `sc16_safe` can be satisfied with no non-agent ever having reviewed the content.
- **Under these hypotheses:** one concrete trace, concrete roles `Rov`, identity hash; checked by `decide`.
- **Does NOT say:** that the overlapping-roles configuration would be deployed; it demonstrates that role disjointness is needed for the stronger reading, not that it is violated in practice.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide); also a witness.
- **Non-vacuity:** it is itself the concrete example.
- **Read depth:** full.

### `ControlStack.AuthInstances.sc16_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesA.lean:58`
- **Says (plain English):** Run the SC-16 gate with true issuers: every operation claims its caller, and is applied only if its issuer is the claimed caller. From the empty state, any list of (issuer, operation) pairs gives (1) the `Good` property of `sc16_safe` (every deployment backed by a same-target approval, content hashing to the approved digest, a reviewed digest with a non-stager reviewer, nonces distinct); (2) every review in the final state came from an operation `(c, review c digest)` really issued by `c`, with `c` not in the adversary set and in the reviewer list; (3) the same for every approval, issued by an approver not in the adversary set.
- **Under these hypotheses:** `U` is a list of adversary issuer ids with no member in the reviewer list and no member in the approver list. Arbitrary roles, hash and (issuer, operation) trace. World premise remaining: the issuer field is the true principal. Hash injectivity is not assumed and not concluded; role disjointness from agents is not assumed.
- **Does NOT say:** that the deployed content is the reviewed content (this needs injectivity, which is absent), that the reviewer is not an agent unless `U` captures all agents and the lists are disjoint from `U`, or that the principals were not deceived or coerced. Conjunct (1) is `sc16_safe` applied to the filtered trace.
- **Kind:** refinement/bridge (reduction of the authenticated run to the plain run, plus a generic trace lemma).
- **Non-vacuity:** NOT SHOWN for the authenticated theorem itself; the underlying `honest_trace_deploys` shows deployments can happen, and `forged16_deploys_without_auth` shows an issuer-filtered run refusing a forgery.
- **Read depth:** full.

### `ControlStack.AuthInstances.forged16_deploys_without_auth`  — `ControlStack/Scenarios/AuthInstancesA.lean:76`
- **Says (plain English):** One fixed trace in which issuer 1 (an agent) issues everything: stage 7, a review claiming to be reviewer 2, an approval claiming to be approver 3, and the deploy. Without checking claims, the deployment of content 7 to target 5 happens; with claims checked against the issuer, nothing deploys, because the review and approval are dropped.
- **Under these hypotheses:** one concrete trace, roles `R0`, identity hash; `decide`. The "no authentication" side uses a claim function that always claims nothing.
- **Does NOT say:** that a real platform can supply an unforgeable issuer, only what the gate does if it does.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).
- **Non-vacuity:** it is itself the concrete example.
- **Read depth:** full.

### `ControlStack.SC16Refinement.concrete_safe`  — `ControlStack/Scenarios/SC16Refinement.lean:256`
- **Says (plain English):** The concrete admission machine has a content store keyed by digest (one entry per digest; first stager kept), a mutable tag table the agent can rewrite, a reviewer log and an approver log, a used-nonce list, a deploy log and a halt flag; the deploy step fetches the bytes by the approved digest from the store and re-hashes them. For any list of concrete operations (puts, tag moves, signed reviews and approvals, deploy requests, halts) with the deployed setting (deploy by digest, not by tag), mapping the final concrete state to the abstract SC-16 state satisfies `Good`: every deployment backed by an approval for exactly its target, content hashing to the approved digest, a reviewed and non-stager-reviewed digest, nonces distinct.
- **Under these hypotheses:** arbitrary roles and hash function and any concrete operation list. Model conditions that are not proved: signatures are modelled as "a row is in a log only if the role holder wrote it" (the caller number is believed; Ed25519 unforgeability and key custody are premises); the controller is single-threaded and each deploy is one atomic step; the Python runtime is assumed to implement this machine (tested only).
- **Does NOT say:** anything about deploy-by-tag (the machine with `byTag = true` fails, see `by_tag_breaks`); that the review was bound to the target in the conclusion (the concrete machine requires a review row for the approved digest and target, but the abstract `Good` that is transferred only mentions the digest); nothing about review competence, or that the runtime code matches the machine.
- **Kind:** refinement/bridge (forward simulation `simulation_run` plus `sc16_safe`).
- **Non-vacuity:** NOT SHOWN for this theorem by name; the concrete machine's deploy step firing is exercised only in `by_tag_breaks` (a `byTag` run and a by-digest run that deploys content 7).
- **Read depth:** full (read `CSt`, `COp`, `stepC`, `depRes`, `fetch`, `α`, `opsOf`, `simulation`, `simulation_run`).

### `ControlStack.SC16Refinement.concrete_reviewed_content`  — `ControlStack/Scenarios/SC16Refinement.lean:261`
- **Says (plain English):** For the concrete admission path, if the hash is one-to-one on the contents that appear in the abstracted final state (deployed contents plus reviewed contents), then every deployed content equals the content in some review, by a reviewer in the reviewer list who is not that content's stager.
- **Under these hypotheses:** arbitrary roles, hash, concrete operation list, deploy by digest; injectivity of the hash on the contents in play (a world assumption passed in as a hypothesis); the same unproved model conditions as `concrete_safe` (signature unforgeability, believed caller ids, atomic single-threaded controller).
- **Does NOT say:** that reviewers are non-agents (that is the separate `concrete_safe_disjoint`, not in this block's list), that review was competent, or that the Python runtime implements the machine. (A reader may notice that the concrete store keeps one entry per digest, so the injectivity hypothesis may be unnecessary for this path; the Lean statement as written still assumes it.)
- **Kind:** refinement/bridge (transfer of `sc16_reviewed_content` through the simulation).
- **Non-vacuity:** the injectivity hypothesis holds for the identity hash; no named witness for the full theorem (`NOT SHOWN`).
- **Read depth:** full.

---

## SC-17: Agent sabotages IaC, Kubernetes or production cluster permissions

**Harm (one sentence):** at an apply, the resulting live permissions exceed the policy ceiling or differ from the approved desired state, or a diff is applied that an independent reviewer did not approve exactly; out-of-band changes between applies are reverted at the next reconcile, not prevented.

**What the Lean claims, taken together, and what they leave to assumptions.** An abstract desired-state model: permission grants, proposals that the author can amend, approvals by a non-author reviewer for a specific diff, and an apply that checks an exact-diff approval and that the resulting state passes a ceiling predicate. For any trace (including out-of-band mutations), every apply record has live = desired, within the ceiling, an exact-diff approval from a non-author reviewer, and no proposal applies twice; after a reconcile live = desired; HALT freezes applies. A separate, simpler model bounds out-of-band drift between applies by `d*W` grants living fewer than `W` ticks, given an assumed attacker rate bound `d` per tick and a trusted scheduler. What is left: that the ceiling predicate captures the intended policy, that the gate is the only writer of desired state, that "live" in the model is the real cluster (the model computes live from desired at apply, so "live = desired" at an apply is by construction), that the reconciler works and the clock is trusted, that credentials are real, and the fact that between applies the live state can exceed the ceiling (stated as a non-claim by the scenario itself).

**World assumptions (from the scenario):**
- `credential_separation` (NOT_PROVED): trusted-role operations are the principal's own act; reduced in Lean by `sc17_safe_authenticated`, residual premise is issuer authenticity.
- `single_apply_path` (NOT_PROVED): the gate is the only writer of desired state; out-of-band mutation is detected at reconcile.
- `ceiling_correct` (NOT_PROVED): the ceiling predicate expresses the intended privilege policy.
- `honest_usefulness` (NOT_PROVED): honest infra changes pass review within acceptable latency.

### `ControlStack.SC17.sc17_safe`  — `ControlStack/Scenarios/SC17Infra.lean:246`
- **Says (plain English):** From any initial grant set (live and desired both equal to it), after any sequence of proposals, amendments, approvals (by any caller), out-of-band live mutations, reconciles, applies and halts, with all four checks on, every record in the `applied` log satisfies: the live grant set recorded at that apply is accepted by the ceiling predicate; it equals the desired grant set recorded at the same apply; there is an approval for that proposal id whose diff equals the diff applied, by a reviewer in the reviewer list who is not the proposal's author. In addition the list of applied proposal ids has no repeats.
- **Under these hypotheses:** The environment (reviewer list, admin list, ceiling predicate `allowed` on whole grant sets) and the initial grants are arbitrary. The initial grants need not satisfy the ceiling; only the result of an apply is checked. Model conditions, not provable in Lean: the recorded "live" after an apply is computed by the model from the desired state (it is not an observation of a real cluster), so the equality of live and desired inside the record is true by construction; the reviewer id is believed; the gate is the only writer of desired state; drift detection sees all of the real live state.
- **Does NOT say:** that live permissions stay within the ceiling between applies (out-of-band grants made after an apply, before the next apply or reconcile, are not constrained by this statement), that the ceiling is correct, that approved diffs are wise, or that the real cluster state equals the model's live state. The statement does not say that an approval was given before the apply, only that one exists in the log at the end.
- **Kind:** general theorem (inductive invariant).
- **Non-vacuity:** `ControlStack.SC17.honest_apply` (by `decide`) shows a reviewed, within-ceiling diff applying.
- **Read depth:** full (read `Diff`, `applyDiff`, `Env`, `Pr`, `Ap`, `AppRec`, `St`, `Op`, `Checks`, `newLive`, `ceilingOk`, `step`, `AppOk`, `Good`, `Inv`).

### `ControlStack.SC17.reconcile_restores`  — `ControlStack/Scenarios/SC17Infra.lean:250`
- **Says (plain English):** If the state is not halted, then performing a single reconcile step (with the deployed configuration, where drift handling is on) leaves live permissions equal to the desired permissions.
- **Under these hypotheses:** only that the starting state has `halted = false` (it can be any state); arbitrary environment. Model condition not proved: the reconciler's write succeeds and sees the whole live state; nothing about how often reconcile happens.
- **Does NOT say:** that drift is prevented or reverted in any particular time; that a reconcile occurs at all; or anything once halted (a halted state ignores `reconcile`). Note also that the model's `oob` operation does not check the halt flag, so after a halt out-of-band grants can accumulate and no reconcile will revert them; the halt theorem for SC-17 concerns only the `applied` log.
- **Kind:** general theorem (one-step; short case analysis).
- **Non-vacuity:** the hypothesis is just `halted = false` (true at the initial state); `ControlStack.SC17.no_drift_detection_breaks` (`decide`) shows an apply reverting an out-of-band grant with drift handling on.
- **Read depth:** full.

### `ControlStack.SC17.halt_freezes`  — `ControlStack/Scenarios/SC17Infra.lean:267`
- **Says (plain English):** If the state is halted, then after running any list of operations the `applied` log is exactly what it was: no new applies are recorded after a halt.
- **Under these hypotheses:** starting state `halted = true`; deployed configuration; arbitrary operations and environment. The halt flag is set by `halt` from a caller in the admin list (believed identity).
- **Does NOT say:** that the whole state is frozen (unlike SC-15/SC-16 versions): out-of-band mutations still change `live` after halt, because `oob` is not guarded by the halt flag (propose, amend, approve, reconcile and apply are all no-ops once halted, but the statement itself only speaks about `applied`). It does not say desired state is unchanged beyond what follows from no applies, nor that real cluster applies stop.
- **Kind:** general theorem (induction; conclusion is about the applied log only).
- **Non-vacuity:** `ControlStack.SC17.no_halt_check_breaks` (`decide`) shows a run where the halt takes effect.
- **Read depth:** full.

### `ControlStack.SC17Drift.drift_bounded`  — `ControlStack/Scenarios/SC17Drift.lean:138`
- **Says (plain English):** In a separate small model with a fixed desired grant set, a stream of out-of-band grants, ticks of a clock and manual reconciles, where a scheduler on every tick reconciles whenever `W` ticks have elapsed since the last reconcile, and where at most `d` out-of-band grants are accepted per tick, at every state reached from the start the number of live grants that are not in the desired state is at most `d` times `W`.
- **Under these hypotheses:** `0 < W` (a theorem hypothesis); `d` and `W` arbitrary naturals; scheduler on (`true`); arbitrary operation list of `oob`, `tick`, `reconcile`. The per-tick limit `d` on out-of-band mutations is not a property of any gate: the model's `oob` step simply ignores an out-of-band grant beyond `d` in the current tick, so it is an assumption about the attacker's write rate. The scheduler and clock are trusted; ticks are operations in the trace. Grants are bare numbers; counting is over the list (duplicates count).
- **Does NOT say:** that live permissions are within the ceiling at any time between reconciles (the file's own `ceiling_exceeded_between_reconciles` shows a live grant outside desired); it bounds the *number* of extra grants, not their severity. It is a separate model from `SC17Infra` (no proposals, approvals or applies; desired never changes), so it does not combine with `sc17_safe` inside Lean. It does not hold without the rate-limit and scheduler premises (the file's witness `no_schedule_unbounded_lifetime` shows the no-scheduler case).
- **Kind:** general theorem (inductive invariant with arithmetic).
- **Non-vacuity:** `ControlStack.SC17Drift.ceiling_exceeded_between_reconciles` (`decide`) shows an out-of-band grant becoming live under `d = 1, W = 3`, so the hypotheses can hold with positive drift.
- **Read depth:** full.

### `ControlStack.SC17Drift.drift_lifetime`  — `ControlStack/Scenarios/SC17Drift.lean:144`
- **Says (plain English):** In the same drift model with the scheduler on, every entry in the "out-of-band grants since the last reconcile" record (each with the clock time at which it was added) was added fewer than `W` ticks before the current clock reading. Together with the separate fact (`live_eq`, not in this block's list) that live equals those recorded grants plus the desired state, this means every currently live out-of-band grant is less than `W` ticks old.
- **Under these hypotheses:** `0 < W`, arbitrary `d`, desired set and operation list; scheduler on; the same attacker-rate and trusted-clock premises as `drift_bounded`. The statement is literally about the model's ghost record `drift` (a bookkeeping list that exists only to state the lifetime), not directly about the live list.
- **Does NOT say:** that a grant dies within any real-time bound unless ticks track real time and the reconciler actually runs and succeeds; nor that the grant did no harm during its lifetime. "Less than `W` ticks" is in model clock units; an adversary cannot slow the clock only if the clock is genuinely trusted.
- **Kind:** general theorem (inductive invariant, `omega` finish).
- **Non-vacuity:** same as `drift_bounded` (`ceiling_exceeded_between_reconciles`, `no_schedule_unbounded_lifetime` which also exhibits a scheduler-on run where the grant is gone after ticks).
- **Read depth:** full.

### `ControlStack.AuthInstances.sc17_safe_authenticated`  — `ControlStack/Scenarios/AuthInstancesA.lean:222`
- **Says (plain English):** Run the SC-17 gate with true issuers (propose, amend, approve, halt claim their caller; `oob`, `reconcile`, `apply` claim nothing). From any initial grants and any list of (issuer, operation) pairs: (1) `Good` holds as in `sc17_safe`; (2) every approval in the final state came from an operation `(c, approve c id)` actually issued by `c`, where `c` is the recorded reviewer, is in the reviewer list, and is not in the adversary set; (3) every proposal record's author is the issuer of a propose/amend operation with that author, id and diff, so "reviewer is not the author" compares two real issuers.
- **Under these hypotheses:** `U` (adversary issuer ids) has no member in the reviewer list (used by (2) only). Premise left: the issuer is the true principal. Conjunct (1) is `sc17_safe` on the filtered trace.
- **Does NOT say:** that the reviewer is not deceived or coerced; that the ceiling is right; nothing is authenticated for `oob`, `reconcile`, `apply` (they claim nothing, so anyone can issue them; the gate's own checks decide their effect).
- **Kind:** refinement/bridge.
- **Non-vacuity:** NOT SHOWN for the authenticated statement itself; `ControlStack.SC17.honest_apply` shows the underlying gate can apply.
- **Read depth:** full.

### `ControlStack.AuthInstances.forged17_applies_without_auth`  — `ControlStack/Scenarios/AuthInstancesA.lean:239`
- **Says (plain English):** One fixed trace: issuer 1 proposes diff `dA` (add grant (1,1,1)) as author 1, issues an approval claiming to be reviewer 2, and requests the apply. Without claim checking, the apply goes through and live permissions become the single grant (1,1,1); with claim checking, the forged approval is dropped and the applied log is empty.
- **Under these hypotheses:** one concrete trace and environment `E0` (reviewer 2, admin 9); `decide`. The two sides compare different fields (live grants without auth, applied log with auth), which is fine here but means this is a comparison of outcomes, not of one field.
- **Does NOT say:** that issuer claims cannot be forged in a real system.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).
- **Non-vacuity:** it is itself the concrete example.
- **Read depth:** full.
