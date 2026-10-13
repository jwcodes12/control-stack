# English statements under test

### Claim 1
## `ControlStack.SC15.sc15_safe`

- **Says (plain English):** Start the merge gate from its empty state and feed it any list of operations in any order (proposals, amendments by the author, reviews, CI runs, merge requests, halts), using the deployed configuration `full` in which all five checks are on. Then every change in the final `merged` log satisfies the "merge-ok" condition: there is a recorded review of that change id whose recorded content equals the merged version's content, by a reviewer who is not the change's author and who holds the role the review was filed under (security role if the review was flagged "security", ordinary reviewer role otherwise); there is a passing CI record for that change id on exactly that content; and, if any path in the merged version's `paths` list is in the environment's `sensitive` list, there is also a review flagged "security" with exact content by a non-author holding the security role.
- **Under these hypotheses:** The environment `E` (reviewer list, security-reviewer list, admin list, sensitive-path list, and a `testsPass` function from content to pass/fail) is arbitrary, and the operation list is arbitrary (any caller ids, contents, paths, declared paths). Model conditions, not provable in Lean: (1) a review record stores the content the gate has for the change at review time, which is treated as "what the reviewer saw"; (2) the `paths` field supplied in `propose`/`amend` is treated as the trusted-diff path list (the model does not tie it to the content, and the adversary chooses it; only the *author-declared* list is distrusted); (3) a CI record's verdict is `testsPass` of the content, i.e. CI is a trusted function of content; (4) the caller number on a review/halt/amend is read as the true identity of the caller; (5) the merge gate is the only way to the protected branch.
- **Does NOT say:** that merged code is free of backdoors (the docstring says so explicitly; the statement is only about which approvals exist). That reviewers or CI are competent, that sensitive-path list is complete, or that the `paths` list matches the real diff. It also does not say a change merges at most once: nothing stops a second merge request for the same change from appending it again to the log (each entry still satisfies the condition); and nothing here concerns who triggers `runCI` or `merge` (they carry no caller).
- **Kind:** general theorem (induction over the trace, via an invariant).

### Claim 2
## `ControlStack.SC15.halt_freezes`

- **Says (plain English):** If the gate's state has its `halted` flag set, then running any list of operations (with the deployed configuration) leaves the entire state exactly unchanged: nothing is proposed, amended, reviewed, CI'd or merged afterwards.
- **Under these hypotheses:** Only that the starting state has `halted = true` (it does not need to be reachable from the empty state), the deployed configuration `full` (halt check on), and an arbitrary environment and operation list. The flag is set by a `halt` operation whose caller is in the environment's admin list (the caller number is believed, as above).
- **Does NOT say:** that a halt happens in time, that merges that occurred before the halt are undone, or that the protected branch cannot be changed by some route outside this gate. It says nothing about who can set the flag beyond the model's `admins` check.
- **Kind:** general theorem (simple induction; proof is mostly unfolding the step function).

### Claim 3
## `ControlStack.AuthInstances.sc15_safe_authenticated`

- **Says (plain English):** Now every operation comes with a *true issuer* (the platform-reported identity), and an operation that claims an identity (propose/amend/review/halt claim their caller) is applied only if the claim equals its issuer; operations claiming nothing (`runCI`, `merge`) always apply. Run the SC-15 gate this way from the empty state on any list of (issuer, operation) pairs. Then (1) the same merge-ok condition as `sc15_safe` holds for everything merged, and (2) every review in the final state corresponds to an operation `(c, review c id sec)` that appears in the trace, issued by `c`, where `c` is the recorded reviewer, `c` is not in the adversary set `U`, and `c` holds the reviewer role (or security role for a security review).
- **Under these hypotheses:** `U` is a list of adversary issuer ids, and the hypothesis is that no id in `U` is in the environment's reviewer list or security list. Conjunct (1) does not actually use that hypothesis (it is `sc15_safe` applied to the filtered trace); conjunct (2) does. Not provable in Lean: that the issuer recorded in the trace is the real principal behind the operation (platform identity premise), that CI results are trustworthy (unauthenticated), and everything listed under `sc15_safe`.
- **Does NOT say:** The docstring says "the change author is the issuer of the proposal", but the stated conclusion has only the two conjuncts above; nothing about proposals is in the Lean statement (it is true by the same filtering but is not stated here, unlike the SC-17 analogue). It does not say the reviewer actually read or understood the content, and does not authenticate CI or `merge` requests.
- **Kind:** refinement/bridge (a reduction to `sc15_safe` via `authRun_eq`, plus a generic "logged records were issued by a trusted principal" lemma).

### Claim 4
## `ControlStack.AuthInstances.forged15_merges_without_auth`

- **Says (plain English):** One fixed trace: issuer 1 issues all four operations: propose change 0 (author 1, content 7, paths [5]), then review change 0 *claiming to be reviewer 2*, then run CI, then merge. In the test environment (reviewer 2, security reviewer 3, admin 9, sensitive path 100, content 13 fails tests), if claims are not checked at all, change 0 merges; if the claim check is on, nothing merges (the forged review is dropped, so the merge has no review).
- **Under these hypotheses:** Just this concrete trace and the concrete environment `E0`; checked by `decide`. The "no authentication" side is modelled by a claim function that always claims nothing, so every operation is applied.
- **Does NOT say:** that authentication is necessary in general, only that for this one trace its removal lets an author self-approve; nor that the claim check could not be bypassed in a real system (it presumes the issuer field is trustworthy).
- **Kind:** negative control (shows a weakened model fails); finite computation (decide).

### Claim 5
## `ControlStack.SC16.sc16_safe`

- **Says (plain English):** From the empty state, after any sequence of staging, slot writes, reviews, approvals, deploy requests and halts (any caller ids, any contents), the deployed configuration `full` guarantees that every entry in the deployment log (a) was backed by an approval with the same nonce and the same target as the deployment, made by someone in the approver list; (b) has content whose hash equals that approval's digest; (c) the approval's digest has a recorded review which is "ok" (the review's recorded content hashes to the digest, its reviewer is in the reviewer list, and the reviewer id differs from the id of the stager of that recorded content). Also the nonces of the deployments are all distinct, so no approval was used twice.
- **Under these hypotheses:** Roles `R` (agents, reviewers, approvers, admins) and the hash function `h` are completely arbitrary (h need not be injective; role lists may overlap). The caller field of each operation is believed. Model conditions: a review records the content the gate found in the store under that digest (the store's first entry with that hash), which is treated as what the reviewer saw; the deploy content is supplied at deploy time and checked against the approved digest; the deploy call has no caller restriction.
- **Does NOT say:** that the deployed content is the content that was reviewed: only that its hash equals the digest that some review has. With a colliding hash the two can differ (see `collision_breaks`). It also says the reviewer differs from the stager of the *reviewed* content, not that the reviewer is a non-agent: a different agent can review it. The approver is only required to be in the approver list, not distinct from the stager or an agent. It does not say that the review preceded the approval, or that the target is a sensible environment.
- **Kind:** general theorem (inductive invariant over traces).

### Claim 6
## `ControlStack.SC16.sc16_reviewed_content`

- **Says (plain English):** If the hash function is one-to-one on the set of contents that appear in this run (the contents that were deployed, together with the contents recorded in reviews), then every deployed content is literally the content some reviewer reviewed: there is a review whose recorded content equals the deployed content, whose reviewer is in the reviewer list and differs from that content's stager.
- **Under these hypotheses:** Arbitrary roles, hash function and operation list, plus the hypothesis that the hash is injective on contents that actually appear in the run. This is a world assumption (collision resistance on the run's contents) that is a hypothesis of the theorem, not something proved; it is only required on the contents in play, not globally.
- **Does NOT say:** that the reviewer was an honest non-agent (an agent other than the stager may review), that the review was competent, or that reviewed content is harmless. Nothing is said if the hash has any collision among those contents; `collision_breaks` shows that case really can deploy unreviewed content.
- **Kind:** general theorem (corollary of `sc16_safe` plus injectivity).

### Claim 7
## `ControlStack.SC16.halt_freezes`

- **Says (plain English):** If the state is already halted, then running any list of operations under the deployed configuration leaves the whole state unchanged, in particular the deployment log: no staging, review, approval or deployment takes effect after a halt.
- **Under these hypotheses:** Starting state has `halted = true` (any state, not necessarily reachable); arbitrary roles, hash, operations; the halt check is on (`full`). The flag is set only by a `halt` operation whose caller is in the admin list (believed identity).
- **Does NOT say:** that deployments already made are undone; that an admin halts in time; or anything about deploying by a route outside the gate.
- **Kind:** general theorem (trivial induction over the trace).

### Claim 8
## `ControlStack.SC16Disjoint.sc16_safe_disjoint`

- **Says (plain English):** Add three hypotheses: no reviewer is in the agent list, no approver is in the agent list, and the hash is injective on contents in play. Then for every deployment, there is a review of exactly the deployed content by a reviewer in the reviewer list, who is not an agent and is not the content's stager, and an approval with the deployment's nonce and target made by an approver in the approver list who is not an agent.
- **Under these hypotheses:** (1) reviewers and agents are disjoint; (2) approvers and agents are disjoint; (3) injectivity of the hash on the run's contents. All three are hypotheses to the theorem (role disjointness and collision resistance are world assumptions); caller identity is believed.
- **Does NOT say:** that identities are authenticated (that is `credential_separation`), that the reviewer is independent of the agent's principal (a human with an agent key, or a coerced reviewer, is out of scope), or anything about review quality. Since "not an agent" is read straight off hypothesis (1) and (2), the non-agent conclusion is essentially a restatement of the role-disjointness hypothesis applied to the reviewer/approver that `sc16_safe` already identifies.
- **Kind:** definitional/trivial (a short corollary of `sc16_reviewed_content` and `sc16_safe`; the added "not an agent" parts are the hypotheses).

### Claim 9
## `ControlStack.SC16Disjoint.overlap_reviewer_is_agent`

- **Says (plain English):** With roles where agent 2 is also a reviewer (agents 1 and 2, reviewer 2, approver 3, admin 4): staging content 7 as agent 1, reviewing it as 2, approving, and deploying leads to a deployment of content 7 to target 5, there is at least one review, and every review recorded is by an agent. So the weaker theorem `sc16_safe` can be satisfied with no non-agent ever having reviewed the content.
- **Under these hypotheses:** one concrete trace, concrete roles `Rov`, identity hash; checked by `decide`.
- **Does NOT say:** that the overlapping-roles configuration would be deployed; it demonstrates that role disjointness is needed for the stronger reading, not that it is violated in practice.
- **Kind:** negative control (shows a weakened model fails); finite computation (decide); also a witness.

### Claim 10
## `ControlStack.AuthInstances.sc16_safe_authenticated`

- **Says (plain English):** Run the SC-16 gate with true issuers: every operation claims its caller, and is applied only if its issuer is the claimed caller. From the empty state, any list of (issuer, operation) pairs gives (1) the `Good` property of `sc16_safe` (every deployment backed by a same-target approval, content hashing to the approved digest, a reviewed digest with a non-stager reviewer, nonces distinct); (2) every review in the final state came from an operation `(c, review c digest)` really issued by `c`, with `c` not in the adversary set and in the reviewer list; (3) the same for every approval, issued by an approver not in the adversary set.
- **Under these hypotheses:** `U` is a list of adversary issuer ids with no member in the reviewer list and no member in the approver list. Arbitrary roles, hash and (issuer, operation) trace. World premise remaining: the issuer field is the true principal. Hash injectivity is not assumed and not concluded; role disjointness from agents is not assumed.
- **Does NOT say:** that the deployed content is the reviewed content (this needs injectivity, which is absent), that the reviewer is not an agent unless `U` captures all agents and the lists are disjoint from `U`, or that the principals were not deceived or coerced. Conjunct (1) is `sc16_safe` applied to the filtered trace.
- **Kind:** refinement/bridge (reduction of the authenticated run to the plain run, plus a generic trace lemma).
