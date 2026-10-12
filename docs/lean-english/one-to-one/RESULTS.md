# **STALE** (formerly **STALE** (formerly **STALE** (formerly **STALE** (formerly **STALE** (formerly **STALE** (formerly **STALE** (formerly G0 formal))))))) comparison results

**Scope:** 26 deployment-stack blocks only. These are gated formal comparisons, **not a compliant blind experiment**: semantic targets were frozen first, but Lean encodings were typed after original-source comparison, with prior implementation familiarity. See [METHOD.md](METHOD.md). Do not promote the English to independently verified on this basis.

The verdict is about the stated model formula, not world-assumption truth, the real deployment, or the complete narrative. Pointwise conclusions and complete predicate definitions are compared; where hypotheses restrict the domain, this is stated explicitly.

| # | Claim | Verdict | Proof | Note |
|---|---|---|---|---|
| 1 | `Accepted` | ENGLISH_WEAKER | [01-Accepted.lean](01-Accepted.lean) | “Only if” permits distinct broker/receiver UIDs. Lean IdentityChecked uses iff and requires them equal. Gated distinctBroker countermodel. |
| 2 | `exclusive_sink` | ENGLISH_WEAKER | [02-exclusive_sink.lean](02-exclusive_sink.lean) | Literal conclusion admits broker as sink writer. Gate proves weaker formula; a separate contextual gate proves equivalence under Accepted plus sink-edge hypotheses. Do not mistake the arbitrary-edge countermodel for an accepted deployment. |
| 3 | `database_custody` | ENGLISH_STRONGER | [03-database_custody.lean](03-database_custody.lean) | Clean broker→database edge refutes receiver-only conclusion. Lean permits receiver OR broker. |
| 4 | `runtime_exclusive` | EQUIVALENT | [04-runtime_exclusive.lean](04-runtime_exclusive.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 5 | `agent_not_receiver_uid` | UNDECIDED | [05-agent_not_receiver_uid.lean](05-agent_not_receiver_uid.lean) | Says quantifies every node; Under restricts a to an agent. Literal reading is gated-false on the receiver itself. Agent-only reading matches Lean; input is internally inconsistent. |
| 6 | `agent_call_legal` | EQUIVALENT | [06-agent_call_legal.lean](06-agent_call_legal.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 7 | `protocol_safe` | EQUIVALENT | [07-protocol_safe.lean](07-protocol_safe.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 8 | `one_use` | EQUIVALENT | [08-one_use.lean](08-one_use.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 9 | `gate_contract` | EQUIVALENT | [09-gate_contract.lean](09-gate_contract.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 10 | `broker_contract` | EQUIVALENT | [10-broker_contract.lean](10-broker_contract.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 11 | `deployment_safe` | EQUIVALENT | [11-deployment_safe.lean](11-deployment_safe.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 12 | `accepted_no_avoided_path` | ENGLISH_STRONGER | [12-accepted_no_avoided_path.lean](12-accepted_no_avoided_path.lean) | Accepted graph may include an agent→reviewer avoided path. Lean excludes paths to sink and database only. |
| 13 | `accepted_path_safety_monotone` | EQUIVALENT | [13-accepted_path_safety_monotone.lean](13-accepted_path_safety_monotone.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 14 | `path_edge_subset` | EQUIVALENT | [14-path_edge_subset.lean](14-path_edge_subset.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 15 | `requested_monotonicity_counterexample` | EQUIVALENT | [15-requested_monotonicity_counterexample.lean](15-requested_monotonicity_counterexample.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 16 | `deployment_broker_safe` | ENGLISH_STRONGER | [16-deployment_broker_safe.lean](16-deployment_broker_safe.lean) | Useful cap-1 one-release model satisfies all premises and publishes one nonce. Lean concludes ≤ cap; strict < cap is false. |
| 17 | `indexed_receipts_sound` | EQUIVALENT | [17-indexed_receipts_sound.lean](17-indexed_receipts_sound.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 18 | `transaction_preserves` | EQUIVALENT | [18-transaction_preserves.lean](18-transaction_preserves.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 19 | `transaction_coherent` | EQUIVALENT | [19-transaction_coherent.lean](19-transaction_coherent.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 20 | `halted_absorbing` | EQUIVALENT | [20-halted_absorbing.lean](20-halted_absorbing.lean) | Entire-state identity exceeds the displayed theorem conclusion but is derivable from the complete Step relation and halted premise. Gated proof establishes equivalence on that domain. |
| 21 | `committed_nonce_unusable` | EQUIVALENT | [21-committed_nonce_unusable.lean](21-committed_nonce_unusable.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 22 | `trace_preserves` | EQUIVALENT | [22-trace_preserves.lean](22-trace_preserves.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 23 | `runtime_trace` | **STALE** (formerly UNDECIDED) | [23-runtime_trace.lean](23-runtime_trace.lean) | English Says changed to distinguish trace proposition from ten-step proof construction. Previous G0 comparison used the old English; no strictly blind gate-passing recheck of this changed block exists. |
| 24 | `final_safe` | EQUIVALENT | [24-final_safe.lean](24-final_safe.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 25 | `replay_was_not_allowed` | EQUIVALENT | [25-replay_was_not_allowed.lean](25-replay_was_not_allowed.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |
| 26 | `omitted_tail_is_accepted` | EQUIVALENT | [26-omitted_tail_is_accepted.lean](26-omitted_tail_is_accepted.lean) | Gate-checked conclusion equivalence; original theorem application also type-checked with its hypotheses. |

**Freshness notice (continuation draft PR #56):** Claim #23 (`runtime_trace`) has changed English and its G0 result is now **STALE**. The historical model-generated, non-strictly-blind comparison does not certify the revised block. G1–G7 (161 claims) have **never** been checked one-to-one. All writing and review to date are model-only; no independent human has reviewed the work.

The corrected English for G0 blocks **1, 2, 3, 5, 12, 16, 20 and 23** is **STALE** against the originally gated comparison inputs. This is a freshness marking, not a new gate verdict. Those original comparisons were themselves not strictly blind. No independent human has reviewed any of this model-written and model-reviewed work; 161 G1–G7 claims have never received one-to-one comparison.

## Corrections to the English

- **Accepted / identity checks:** for nodes with distinct ids, equal UIDs hold **iff** their ids are the broker/receiver pair. This requires broker and receiver to share a UID, while all other distinct-id pairs have different UIDs. The comparison identifies this necessary correction; the current English definition is not an exact expansion.
- **exclusive_sink:** “Every authority edge in the accepted IR targeting the sink has the receiver as its source.” This is the exact conclusion. The weaker disjunction is nevertheless logically equivalent on the full accepted sink-edge domain; both gate results are retained.
- **database_custody:** “Every authority edge in the accepted IR targeting the database has the receiver **or broker** as its source.”
- **agent_not_receiver_uid:** “Every **agent** node in the accepted IR has a UID different from the identified receiver node.” Align Says with Under.
- **accepted_no_avoided_path:** “No agent has a path to the **sink or database** avoiding the broker and receiver.” Other targets are permitted.
- **deployment_broker_safe:** “The published nonce count is **at most** the cap,” with no duplicates and used approvals. Exactly filling the cap is permitted.
- **halted_absorbing:** if reproducing the original displayed conclusion, say “the halted flag remains true and the release count is unchanged.” Full-state identity is additionally derivable in this model, as the gated comparison proves, but is not the displayed theorem statement.

## Additional provenance proof

[ProvenanceDraft.lean](ProvenanceDraft.lean) proves ReviewProvenance, ApprovalProvenance, their Step/Trace preservation, and deployment_broker_provenance. The separate frozen [provenance.statement.lean](provenance.statement.lean), proof, nonce log and SHA receipt retain the proofledger-gate result. The nonempty witness uses the existing useful broker trace with spent = 1.

Published nonces have used approvals, an approver signer, an agent owner, an existing artifact, a current review recorded under a reviewer role, and a retained lease belonging to that agent. No exact release digest/destination matching, real runtime correspondence, content harmlessness, or immutable original-reviewer identity is claimed.

## What remains

G1–G7 (161 headline claims) have not been reached. A strictly blind first-exposure check of G0 also remains, because this pass disclosed prior familiarity and did not freeze typed Lean before source comparison. The local imports adapter is reviewable here; no upstream proofledger commit was made. No bus report was sent: the latest user message authorizes reading the relay and resuming the existing goal, and explicitly treats the relay as information.

The original deployment handoff is already completed by the current checkout’s END-STATE.md. Read-only GitHub receipts in release-pr-summary.json show PRs #45–53 merged externally and #54 still draft/open; no branch changes, merges or pushes were performed in this review.
