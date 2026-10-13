# Blind g0n2 Phase B results

All eight **back-translated core statements** are EQUIVALENT to the original declarations. This does not certify every explanatory sentence in the English: the corrections below matter.

All eight Phase A SHA-256 values in `back/BACK-HASHES.json` matched. Every back file compiled as written with `lake env lean`; no typing/syntax repairs were needed. Unchanged copies and `typed/HASHES.json` were saved at **2026-10-13T04:10:31.055431+00:00, before any original declaration was opened**. Each `compile-fixes/<n>.diff` records the empty diff and no meaning change.

The saved statements retain the frozen back definition body, reproduce the inspected original signature, and check the original declaration directly against that signature. Each Claim proves by reflexivity that both full statement shapes decompose into the specified hypotheses and conclusions, then proves **BackConclusion ↔ OrigConclusion at the same parameters and under the same hypotheses** with `Iff.rfl`. No comparison obtains equivalence from the truth of two closed theorems. Claims 1 and 4 align differently ordered binders by name. For the fixed instances (6 and 8), the expressions themselves coincide. There are no definition claims in this batch. `comparison-map.json` records source signatures and frozen hashes.

Both targets were separately checked with the supplied deterministic gate. The concrete Witness propositions avoid empty receipts, mere denial steps, and zero-budget examples where applicable. Claim proofs have no axioms except claim 8's permitted `propext` and `Quot.sound`; witness proofs use at most those same permitted axioms. No prohibited proof token or additional axiom was accepted.

| Claim | Verdict | Receipts | Note: pointwise comparison |
| --- | --- | --- | --- |
| 1 `indexed_receipts_sound` | **EQUIVALENT** | [Claim PASS](bg0n2_1.receipt.json), [Witness PASS](bg0n2_1.witness.receipt.json) | Same `R`, table, start, receipts and verification hypothesis; same `Trace` between interpreted start and recorded end. Witness: ten accepted receipts with increasing spent. |
| 2 `transaction_preserves` | **EQUIVALENT** | [Claim PASS](bg0n2_2.receipt.json), [Witness PASS](bg0n2_2.witness.receipt.json) | Under identical `Safe s` and `Step roles s t`, `Safe t ↔ Safe t`. Witness: first actual release, spent increases. |
| 3 `transaction_coherent` | **EQUIVALENT** | [Claim PASS](bg0n2_3.receipt.json), [Witness PASS](bg0n2_3.witness.receipt.json) | Under identical `Coherent s` and `Step roles s t`, `Coherent t ↔ Coherent t`. Witness: nonce 1 enters consumed history on the first release. |
| 4 `committed_nonce_unusable` | **EQUIVALENT** | [Claim PASS](bg0n2_4.receipt.json), [Witness PASS](bg0n2_4.witness.receipt.json) | Under identical nonce equality, the same negated `Allowed` proposition, for every state, roles, requests, approvals, lease and clock. No initial `Allowed` premise added. Witness additionally shows an initially allowed release followed by same-nonce rejection. |
| 5 `trace_preserves` | **EQUIVALENT** | [Claim PASS](bg0n2_5.receipt.json), [Witness PASS](bg0n2_5.witness.receipt.json) | Under identical `Safe s` and `Trace roles s t`, `Safe t ↔ Safe t`. Witness: full trace from cap 2, ending after two releases. |
| 6 `final_safe` | **EQUIVALENT** | [Claim PASS](bg0n2_6.receipt.json), [Witness PASS](bg0n2_6.witness.receipt.json) | Identical fixed expression `TrustedBroker.Safe s10`. Witness independently checks spent, cap and releases equal 2; consumed is `[2,1]`; both leases have used 1. |
| 7 `replay_was_not_allowed` | **EQUIVALENT** | [Claim PASS](bg0n2_7.receipt.json), [Witness PASS](bg0n2_7.witness.receipt.json) | For every clock, approval and lease, the same `¬ Allowed R s8 now q8 a' l'`. Witness: `q8 = q7`, concrete allowed first release, and stored approval subsequently used. |
| 8 `omitted_tail_is_accepted` | **EQUIVALENT** | [Claim PASS](bg0n2_8.receipt.json), [Witness PASS](bg0n2_8.witness.receipt.json) | Identical fixed Boolean acceptance equality. Witness checks lengths 10/9, distinct recorded ends 10/9, full acceptance, and rejection of the specific middle-release and denial deletions. |

## Corrections to the English

1. **Claim 1, “A shorter list also passes.”** This is too broad if read as any shorter list. Claim 8's witness checks that the nine-receipt prefix passes, while deleting the middle release or the denial does not. Replace with: **“A valid prefix can also pass: in this transcript the first nine receipts are accepted. Arbitrary deletions need not pass, because the remaining state ids may no longer form a chain.”**

2. **Claim 4, “A different nonce for the same digest can be approved and released again (limited only by lease and global budget).”** The parenthetical is wrong. `Allowed` also requires a live broker, the agent role, matching stored unused approval and its fields, an approver signer, approval and lease expiry tests, lease ownership and non-revocation, positive cost, artifact presence and integrity, a review entry, and nonce freshness. Replace with: **“This theorem does not rule out another release of the same digest under a different nonce. Such a release still has to satisfy the entire `Allowed` guard, including a matching unused approval, the role and expiry checks, artifact and review checks, and lease and global budgets.”** It is permission left open by this result, not an unconditional existence claim or a sink guarantee.

3. **Claim 6, the Kind label and placement of the numeric facts.** The original `final_safe` proof is an application of `trace_preserves` to `initial_safe` and `runtime_trace`; it is not itself a `decide` or native computation. Its explicit conclusion is only `Safe s10`. The numeric equalities follow from the fixed definitions and are separately stated by `final_counts`; the gated Witness also checks them. Replace with: **“The replayed model state `s10` satisfies `Safe`. This concrete instance follows from `runtime_trace` and the general `trace_preserves` theorem. In this fixed instance, spent and cap are both 2; those numeric equalities are separate facts about `s10`.”** Kind: **“Concrete-instance theorem derived from a checked model trace.”**

4. **Claim 7, “closed by `rfl`.”** The theorem is a direct application of `committed_nonce_unusable`; `rfl` discharges the nonce equality supplied to that theorem. Replace with: **“This is a direct instance of `committed_nonce_unusable`; the required equality between the two request nonces is proved by `rfl`.”**

5. **Claim 8, “indistinguishable by this checker from a complete one.”** This should refer to acceptance, not identical visible input or output state. The lists have different lengths and recorded ends, as the witness checks. Replace with: **“Both the full transcript and this nine-receipt prefix return acceptance. Acceptance alone therefore does not establish that all real events were recorded.”**

## Ambiguities exposed

- **Claim 1 — scope and intermediate states.** The original conclusion is the `Trace` relation between the two endpoints. It does not return a receipt-authenticity certificate or a runtime ordering certificate. Its table premise already certifies every table operation at every id. The English respects the real-log and sink exclusions; its shorter-list wording needs correction 1. A checked table is an assumption, not a proof that the runtime used it.

- **Claim 2 — exactly what Safe means.** `Safe` is precisely the four stated constraints: spent ≤ cap, releases ≤ spent, consumed nonces have no duplicates, and every stored lease has used ≤ budget. It says nothing about approvals, reviews, digests or destinations. The model-only, integrity-tampering and clock-rollback exclusions are respected: `Step` never introduces `intact = false`, and time has no monotonicity requirement.

- **Claim 3 — “approval exists and is marked used.”** This means `∃ a, s.approvals nonce = some a ∧ a.used = true`, pointwise for every nonce, exactly as in `Coherent`. It does not refer to an external database or log. The stated invariant limitation is respected; it does not assert the other approval fields are correct.

- **Claim 4 — applying committed versus making a legal release.** The result holds even for inputs that were not allowed in the pre-state. It concerns the state produced by `committed`, and any offered clock, approval and lease for a request with the same nonce. The original proof reads the stored approval and contradicts its required unused flag; no coherence premise is needed. The sink and SQL-refinement exclusions are respected. The budget-only description of a different nonce is not respected by the actual full guard and needs correction 2. This particular declaration is a post-state result; a lifetime “at most once” claim through later transitions additionally needs the model's transition facts.

- **Claim 5 — “any finite sequence.”** This is finite relational closure of `Step`, including the empty trace and arbitrary legal serial order. It is not a concurrency implementation proof or a guarantee against real rollback or partial sink effects. The stated exclusions are respected when “excludes” means those real operations are not separately modelled or justified by this theorem.

- **Claim 6 — concrete facts versus invariant content.** The numeral 2 comes from this instance's definitions, not the meaning of `Safe` in general. The real-database, sink, approval/review and transcript-completeness exclusions are respected. Neither the equivalence proof nor its witness establishes authenticity of the archived runtime log.

- **Claim 7 — reason for a model rejection versus cause of the recorded denial.** The guard failure is universal over offered clock/approval/lease values, and `q8` is definitionally the same request as `q7`. The receipt for the denial uses `Step.deny`, an unconditional identity transition. Consequently replay acceptance does not attest why a real denial happened. The English explicitly says this and correctly excludes guarantees about different nonces.

- **Claim 8 — completeness versus chain consistency.** The theorem establishes acceptance of this particular prefix. It neither asserts that truncation occurred nor certifies completeness of any real transcript. These negative-control limits are respected. “Indistinguishable” should be restricted to acceptance as in correction 5; removing a middle event or the denial from these fixed receipts instead breaks their id chain.

The gate trusts the project imports as configured by `PL_IMPORTS`; these comparisons certify correspondence to that imported model, not runtime refinement. `run_gate_blind.py` is the supplied runner relocated into this output directory: the project-root depth and gate-helper lookup receive the necessary path adjustments, and the file glob selects `bg0n2_*`. Existing imports suffice. [The exact runner diff](run_gate_blind.diff) records those path/glob changes. The supplied `leangate_imports.py`, including every banned-token and axiom check, is unchanged.

Reproduce all eight statement checks and all sixteen target gates from the repository root:

```sh
python3 -B docs/lean-english/one-to-one/blind-g0n2/regate.py
```

`regate.py` reads the saved files and rewrites only receipts/logs, plus transient check files that the deterministic gate removes. It checks all eight expected ids, separately gates Claim and Witness, and exits nonzero on any failure. `-B` and the script's bytecode setting prevent Python cache writes outside this directory. The clean-state check removes prior gate receipts and the empty transient directory before regenerating them; `regate-validation.json` records unchanged input hashes and the missing-input failure check.
