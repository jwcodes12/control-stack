# Blind g3n1 Phase B results

**Eight EQUIVALENT; two ENGLISH_WEAKER.** Every comparison and every non-vacuity Witness passed its own deterministic gate. The gate helper is byte-identical to the supplied `leangate_imports.py`; its banned-token checks, nonce check and allowed-axiom checks are unchanged. Only `propext` and `Quot.sound` appear in the successful final axiom reports.

All ten back files compiled as written. Their hashes matched `back/BACK-HASHES.json`; byte-identical copies and `typed/HASHES.json` were saved at **2026-10-13T04:13:22.934941+00:00**, before any original declaration was opened. No compile repairs were necessary; `compile-fixes/<n>.diff` records that fact for each claim. No git, network downloads, source edits or prior comparison results were used.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — `SC15.sc15_safe` | EQUIVALENT | [comparison](bg3n1_1.receipt.json), [Witness](bg3n1_1.witness.receipt.json) | For arbitrary `E,s`, both conclusions say `∀ c ∈ s.merged, MergeOk E s c`; identical empty-state/full-run instantiation. |
| 2 — `SC15.halt_freezes` | EQUIVALENT | [comparison](bg3n1_2.receipt.json), [Witness](bg3n1_2.witness.receipt.json) | Same arbitrary environment, state and operations, same `s.halted = true` premise, same equality of the entire state. |
| 3 — `AuthInstances.sc15_safe_authenticated` | EQUIVALENT | [comparison](bg3n1_3.receipt.json), [Witness](bg3n1_3.witness.receipt.json) | Exclusion from each role list iff exclusion from their append. The existential issuer/operation formulation iff membership of the explicitly reconstructed issued review, pointwise in arbitrary logs. |
| 4 — `AuthInstances.forged15_merges_without_auth` | ENGLISH_WEAKER | [comparison + strictness](bg3n1_4.receipt.json), [Witness](bg3n1_4.witness.receipt.json) | `Orig → Back` only as log conclusions: exact unchecked singleton implies id-0 membership; membership does not determine its content, author, paths or log cardinality. Checked empty-log conclusion is identical. |
| 5 — `SC16.sc16_safe` | EQUIVALENT | [comparison](bg3n1_5.receipt.json), [Witness](bg3n1_5.witness.receipt.json) | Both conclusions are `Good R h s`, pointwise for arbitrary roles, hash and state, with the same full run. |
| 6 — `SC16.sc16_reviewed_content` | EQUIVALENT | [comparison](bg3n1_6.receipt.json), [Witness](bg3n1_6.witness.receipt.json) | List-membership injectivity iff `Set.InjOn` on deployed-or-reviewed contents, for every hash/state. Review conclusions are identical. |
| 7 — `SC16.halt_freezes` | EQUIVALENT | [comparison](bg3n1_7.receipt.json), [Witness](bg3n1_7.witness.receipt.json) | Same halted-state hypothesis and entire-state equality for arbitrary roles, hash, state and operations. |
| 8 — `SC16Disjoint.sc16_safe_disjoint` | EQUIVALENT | [comparison](bg3n1_8.receipt.json), [Witness](bg3n1_8.witness.receipt.json) | Same two role-disjointness hypotheses; equivalent list/set injectivity premise; identical exact-content review and nonce/target approval conclusions. |
| 9 — `SC16Disjoint.overlap_reviewer_is_agent` | ENGLISH_WEAKER | [comparison + strictness](bg3n1_9.receipt.json), [Witness](bg3n1_9.witness.receipt.json) | `Orig → Back` only as log conclusions: exact deployment `[⟨0,5,7⟩]` implies existence at target 5 with content 7; existence omits nonce 0 and singleton cardinality. Review conclusions are identical. |
| 10 — `AuthInstances.sc16_safe_authenticated` | EQUIVALENT | [comparison](bg3n1_10.receipt.json), [Witness](bg3n1_10.witness.receipt.json) | Combined per-adversary role exclusions iff the original two hypotheses. Explicit issued review/approval membership iff the original existential issuer/operation conclusions, for arbitrary observed states. |

Each `bg3n1_<n>.statement.lean` contains the frozen back proposition as `BackClosed` (only its declaration name and surrounding namespace change), a pointwise `BackAt`, the source conclusion as `OrigAt`, and the source theorem type as `OrigClosed`. Each proof checks `original_type : OrigClosed` against the named original declaration. Its `claim` proves the comparison; its `witness` proves a concrete non-degenerate instance. Reconstruction iff clauses connect the frozen back proposition to the parameterized conclusion, and separate iff clauses establish the hypothesis translations where necessary.

For 1, 3, 5, 6, 8 and 10, the pointwise comparison even holds for arbitrary observed states, independently of reachability. For 2 and 7, it is stated under the same halted-state premise. These are structural proofs using the given conclusion as input in each direction; they do not call the original safety theorem to prove both sides of an iff.

For the closed finite-computation claims **4 and 9**, the comparison deliberately abstracts the *observed logs* before comparing their conclusions. It does **not** prove an iff between two closed true propositions. In claim 4, a log containing `⟨0,1,999,[5],[5]⟩` with an empty checked log satisfies `BackAt` and falsifies `OrigAt`. In claim 9, deployment `⟨99,5,7⟩` with review `⟨7,2,7,1⟩` satisfies `BackAt` and falsifies `OrigAt`. Both strictness counterexamples are inside the gated Claim. They distinguish information expressed by the log predicates; they are **not** assertions that the named fixed trace produces those counterexample states. The separately gated Witnesses confirm the actual named traces produce the original exact logs. No `DIFFERENT` verdict about their executions is being asserted.

Witnesses are substantive: claims 1 and 3 have an actual merge and review; 5, 6, 8 and 10 have an actual deployment, review and approval, with the required role/injectivity premises; 2 and 7 have a halted state with an existing protected log and a nonempty list of attempted operations; 4 demonstrates the checked/unchecked split; 9 records the actual overlapping-role deployment and agent review.

`regate.py` imports the copied runner's gate, project path and imports, then checks all ten saved statements and separately gates all ten claims and all ten Witnesses. It rewrites only the twenty JSON receipts, creates/removes the gate's transient Lean check files, and exits non-zero for missing inputs, an unexpected statement inventory or any failed gate. The clean-state rerun removes all prior live receipts and the empty scratch directory first; its evidence is in `clean-regate-test.json`. Saved statement/proof hashes are in `FROZEN-COMPARISON-HASHES.json`. Failed development attempts are preserved under `attempts/1/` and `attempts/2/`; `attempts/3/` preserves the successful receipts before the clean-state rerun. The final table refers only to the live receipts.

Run from the repository root:

```bash
python3 docs/lean-english/one-to-one/blind-g3n1/regate.py
```

The runner's diff is saved in `runner-relocation.diff`: imports and glob change as requested, and the project-root ancestor changes from `parents[3]` to `parents[4]` because the copy lives one directory deeper. The gate implementation itself is unchanged from the supplied helper.

## Corrections to the English

**Claim 4 — replace the Says sentence with:**

> In `E0`, run exactly `[(1, propose 1 0 7 [5] [5]), (1, review 2 0 false), (1, runCI 0), (1, merge 0)]` from the empty state under `full`. With a claim function that always returns `none`, the final merged log is exactly the one-element list whose change has id 0, author 1, content 7, paths `[5]` and declared paths `[5]`. With `claim15`, the final merged log is empty.

This states the original exact-list conclusion and fills in the ordinary-review flag and declared paths. The existing limitations about this one trace and trusted issuer identity can remain.

**Claim 9 — replace the Says sentence with:**

> With `Rov` (agents `[1,2]`, reviewers `[2]`, approvers `[3]`, admins `[4]`) and the identity hash, run exactly `[stage 1 7, review 2 7, approve 3 0 7 5 0, deploy 1 0 5 7]` from the empty state under `full`. The deployment log is exactly the one-element list `[(nonce 0, target 5, content 7)]`, the review log is nonempty, and every recorded reviewer belongs to `Rov.agents`.

This fixes nonce, slot and deploy caller and retains the original exact deployment-log conclusion. It deliberately leaves the review-log conclusion at nonempty/all-agent, as in the source theorem.

**Claims 6 and 8 — clarify the stager phrase:**

> The reviewer differs from the stager id stored in that review record, which comes from the first content-store entry whose hash matches the reviewed digest.

For claim 8, retain the additional conclusion that this reviewer and the matching approver are not members of `R.agents`. This wording resolves the ambiguity without adding authentication, principal independence or a condition about every person who has ever staged equal content.

## Ambiguities exposed

The strongest discrepancy is **existence versus exact list equality**. Claims 4 and 9 describe concrete runs, but the blind propositions extracted only existence of a matching entry. Their English is true as a summary, yet omits information in the original conclusions. Knowing both named computations are true would hide this difference; hence the pointwise log-predicate comparison and explicit strictness counterexamples above.

Claim 9's Phase A note specifically flagged omitted approval nonce, approval slot and deploy caller. Its chosen values (0, 0, 1) happen to match the source trace. That agreement does not remove the English ambiguity, and nonce 0 is also absent from the extracted deployment conclusion. Claim 4 likewise leaves the review security flag and declared paths implicit; its use of the project constant `forged15` supplies these values, so they cause no additional Lean proposition mismatch here.

“The content's stager” in 6 and 8 means the review record's `stager` field. The content-store lookup takes the first matching hash entry; it is not a universal statement about all stagers of numerically equal content. Equality of content does not establish a unique real-world author or principal.

All ten **Does NOT say** blocks are respected by the frozen propositions and source conclusions:

- **1:** No backdoor-freedom, competence, test adequacy, complete sensitive list or real-diff guarantee. Duplicate merge entries remain allowed. `runCI` and `merge` carry no caller.
- **2:** No timely halt, rollback or protection against routes outside the gate. Admin membership authorizes the model's halt; true identity remains a premise.
- **3:** No proposal-authorship conjunct appears in this theorem, despite the docstring. No reviewer-understanding guarantee and no issuer authentication for CI or merge events.
- **4:** Only the concrete forged trace is demonstrated; universal necessity or real-platform unforgeability is not concluded. The weaker exact-log description above is a loss of stated information, not an added security guarantee.
- **5:** Hash agreement does not imply content identity for arbitrary hashes. A reviewer can be another agent; an approver need only have its role. No review-before-approval or meaningful-target condition is stated.
- **6:** Injectivity is a hypothesis restricted to deployed/reviewed contents. No honest non-agent, competent review or harmless-content conclusion. Failure of injectivity removes this theorem's guarantee; it does not imply every colliding run fails.
- **7:** No rollback, timely intervention or guarantee about bypass deployment routes. The theorem concerns the entire state, including slot writes omitted from the informal operation list in Says.
- **8:** Role-disjoint ids do not prove authentication or independence of real principals. Review quality remains outside the theorem.
- **9:** The witness shows a permitted overlapping-role model, without claiming this is a deployed configuration. It demonstrates why the stronger non-agent reading needs role separation.
- **10:** No content identity from digest equality, no reviewer/non-agent separation unless encoded by the adversary/role hypotheses, and no absence of deception or coercion. Every SC16 operation, including deploy, claims its caller; the baseline deployment step still imposes no deploy-caller role restriction.

The run-scoped injectivity formulations in 6/8 and issuer-existential formulations in 3/10 are **equivalent presentations**, not stronger English assumptions. Shared project predicate vocabulary (`MergeOk`, `Good`) was reused in several blind statements; its definitions were also inspected against the English. The gate certifies comparisons of Lean propositions and witnesses, while trusted identities, accurate paths, competent humans and the sole-gate deployment/merge route remain world premises.
