# Blind g6n3 — Phase B results

All six frozen Back statements are **EQUIVALENT** to their original theorem statements in the required pointwise sense. Every comparison and every non-vacuity witness passed the deterministic gate, including the final clean-state replay. These verdicts concern the principal theorem encoded by each Back file; they do **not** certify every auxiliary assertion in the English. In particular, claim 6's assertion that its fairness predicate is “strictly weaker” is incorrect as a general implication claim.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — `progress_interleaved` | EQUIVALENT | [Claim PASS](bg6n3_1.receipt.json), [Witness PASS](bg6n3_1.witness.receipt.json) | Executer identity is ignored by `step`; the requester chosen by Back loses no generality. |
| 2 — `Concrete.crash_tolerant_progress` | EQUIVALENT | [Claim PASS](bg6n3_2.receipt.json), [Witness PASS](bg6n3_2.witness.receipt.json) | Count = 1 entails membership; the original's extra membership conjunct adds no strength. |
| 3 — `lossy_safe` | EQUIVALENT | [Claim PASS](bg6n3_3.receipt.json), [Witness PASS](bg6n3_3.witness.receipt.json) | Identical pointwise `Good` proposition, with the same legality and fixed configuration. |
| 4 — `lossy_rounds` | EQUIVALENT | [Claim PASS](bg6n3_4.receipt.json), [Witness PASS](bg6n3_4.witness.receipt.json) | Round membership/index fairness and the legality formulations coincide; continuation execution equals concatenation. |
| 5 — `lossy_halt_keys` | EQUIVALENT | [Claim PASS](bg6n3_5.receipt.json), [Witness PASS](bg6n3_5.witness.receipt.json) | `runLH ... true` equals `runL ... true` on all states and operation lists. |
| 6 — `tagged_rounds` | EQUIVALENT | [Claim PASS](bg6n3_6.receipt.json), [Witness PASS](bg6n3_6.witness.receipt.json) | Splitting at a round and indexing it coincide, including its starting state. The auxiliary strict-weakening assertion needs correction. |

## Evidence and method

All six original Back files compiled as written, without any repair. Their bytes matched [back/BACK-HASHES.json](back/BACK-HASHES.json). Identical copies and [typed/HASHES.json](typed/HASHES.json) were saved at **2026-10-13 05:40:45 UTC, before opening any original declaration**. Each [compile-fixes](compile-fixes) record is explicitly a no-op, and [compile-logs](compile-logs) records the successful original compilation.

Each statement file embeds its frozen Back definition and a universalized copy of the original declaration's signature. `BackShape` and `OriginalShape` are proved by definitional equality, mechanically connecting those signatures to the extracted outcomes. `Pointwise` compares those outcomes under shared hypotheses. For claims 4 and 6, `Projection` additionally proves that Back's membership plus universally quantified continuation count is precisely its family of pointwise conclusions for all legal continuations. The original theorem also universally quantifies its continuation parameter. Named delivery rows versus existentially supplied rows are handled by unpacking/packing the same row; neither outcome depends on which witness of the row hypothesis is supplied.

The comparison proofs do not call any of the six original target theorems. They use transition equality, list and count facts, and list decomposition. Thus equivalence does not arise from asserting that two closed true theorems imply each other. Some comparisons hold even without their stated hypotheses because the pointwise expressions are equal; this is a structural fact rather than an appeal to their truth.

The source signatures are saved in [original-signatures.txt](original-signatures.txt). Final statements and proofs are frozen in [STATEMENT-PROOF-HASHES.json](STATEMENT-PROOF-HASHES.json).

[run_gate_blind.py](run_gate_blind.py) is the supplied runner relocated into this output directory. Its only configuration changes are directory resolution, the claim glob, and `PL_IMPORTS`. The extra directory level requires `ROOT` to use `parents[4]` instead of `parents[3]`; the relocation is recorded in [runner-relocation.txt](runner-relocation.txt). The gate helper is copied byte-for-byte from the permitted `leangate_imports.py`. Its banned-token checks, nonce assembly, kernel compilation, and axiom whitelist are unchanged. Trusted imports are:

```text
ControlStack.Scenarios.SC26Liveness
ControlStack.Scenarios.SC26LossyLiveness
ControlStack.Scenarios.SC26LossyHalt
```

`PL_LEAN_PROJ` is the repository root. Each receipt records the statement, proof and gate hashes, imports, project path, statement check and target-specific axiom report. All reported axioms belong to the gate's permitted set `propext`, `Classical.choice`, `Quot.sound`. Unused-binder warnings in copied signatures are harmless; they do not bypass any gate check.

[regate.py](regate.py) reads the saved files and independently gates `claim` and `witness` for every id `bg6n3_1` through `bg6n3_6`. It does not use existing receipts or regenerate statements/proofs. A failed statement check, failed target check, missing file or other exception causes a failing receipt and a nonzero process exit. Run from the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g6n3/regate.py
```

The final replay began with all receipts, gate temporary files and Python cache removed. It exited **0** and recreated all twelve passing receipts. The saved Back, typed, statement and proof hashes remained unchanged. The replay's only persisted outputs were receipts; [clean-replay-check.json](clean-replay-check.json) records this check. Temporary gate files were removed by the unchanged helper.

## Pointwise comparisons and hostile reading

**Claim 1.** With the same `R`, cap, invariant starting state, request, approval and four legal adversary lists, Back fixes the honest execute caller to `r.requester`, while Orig quantifies any caller `c`. The execute transition matches `.execute _ id`, so both produce the same state even for a caller distinct from the requester. Singleton appends and cons notation describe the same trace. The three disjuncts therefore coincide pointwise. The witness has a genuine independently approved request, a positive amount and cap, and successful payment using caller 88. All three “Does NOT say” qualifications are respected: halt and cap exhaustion remain possible exits; no temporal bound appears; the conclusion does not assert a count.

**Claim 2.** Fix a legal reachable prefix, a delivery row with id `k`, legal interleavings and the same not-halted-before-recover hypothesis. The traces coincide. Back says `count k = 1`; Orig says membership and `count k = 1`. Back → Orig uses positivity of that count to prove membership; Orig → Back takes the count conjunct. Neither direction uses a progress theorem. The witness includes crashes before recovery, between recovery and bank processing, and afterward, with an actual delivery intent and final count one. All three “Does NOT say” qualifications are respected. The schedule is assumed, later halt is allowed, and payload equality/authorization are absent from this conclusion. The concrete wire persists across crashes in this machine.

**Claim 3.** For each fixed legal lossy trace, both outcomes are literally `Good R cap (α (runL R cap true cinit ops))`. The witness performs a positive-value authorized setup, recovery, duplication, drop and indexed delivery, ending with one payment and spent amount 10. The “Does NOT say” qualifications are respected: idempotent processing and halt-respecting recovery are fixed configuration choices, and the statement provides no loss-tolerant liveness guarantee. `Good` also includes correspondence to an existing reserved request; spelling that out would make the English fuller.

**Claim 4.** The same legal reachable prefix supplies a row with id `k`. Legality over flattened `roundOps` is equivalent to legality over each round's two lists because the inserted recovery is automatically legal. A member satisfying `Delivers` is equivalent to a valid list index satisfying it. For every legal continuation, running the window and then the continuation equals running their concatenation. These equivalences preserve the final-window not-halted hypothesis. The witness uses one genuinely delivering round and a continuation that duplicates and processes an existing message again, retaining count one. All three “Does NOT say” qualifications are respected: there is no independent numerical loss bound, all-drop windows need not progress, and not halted at the window end is assumed. The English should explicitly allow an arbitrary suffix after the designated bank processing.

**Claim 5.** Back uses the configurable runner `runLH` with recovery flag true; Orig uses `runL` with dedup true. Their single-step functions agree in every operation case, so the complete runs agree for arbitrary starting states, without reachability or invariant assumptions. For the same halted state, legal continuation and queried key, bank-key membership and the allowed origins coincide. The witness starts halted with an empty ledger and a positive-value message in flight, then duplicates, drops, crashes, attempts recovery and delivers it. Thus a key really can land after halt. All “Does NOT say” qualifications are respected: the result excludes keys outside the old ledger/wire union, does not freeze the ledger, does not require a halt to occur within the trace, and uses halt-respecting recovery.

**Claim 6.** Legality is translated as in claim 4. Back's `before ++ r :: after` split corresponds to Orig's index `j`, with `before = take j`; the same tagged starting state is passed to `DeliversT`. The final outcomes coincide for every legal continuation by `runT_append`, and no additional halt hypothesis is inserted. The non-vacuity witness reaches the logged state legally, performs `pcRound` (transmit, recover, drop the earlier copy, indexed delivery of the newer copy), and retains exactly one payment after another duplication and delivery. The three “Does NOT say” qualifications are respected when interpreted as denying unconditional scheduling, retransmission and authorization/payload conclusions. However, the auxiliary claim of strict weakening is false as a general comparison of predicates; the separately gated witness includes the reverse counterexample described below.

## Corrections to the English

**Claim 6 — replace the strict-weakening sentence.**

> The per-copy premise allows some delivery traces with earlier drops that the drop-free `Delivers` premise excludes; `per_copy_weaker` supplies one such example. The two raw predicates are not ordered by implication: `Delivers` can hold even when the intent is already acknowledged and this recovery emits no new tagged copy.

This is a substantive correction. `per_copy_weaker` proves an example of `DeliversT ∧ ¬ Delivers`, not a universal implication. Our gated `FairnessAudit`, included in claim 6's **Witness**, proves the other separation in a legal reachable, unhalted state. Start with `setupOps`, then recover, process key 0 and acknowledge row 0. Choose the round `([], [bankProcess 0])`. Its syntactic `Delivers` premise holds. The intent is acknowledged, so recovery's batch is empty and `DeliversT` fails. The state still satisfies the delivery-row and not-halted requirements relevant to claim 4. Therefore this issue cannot be dismissed as an unreachable or halted-state artifact. The principal `tagged_rounds` theorem and its Back translation remain equivalent.

**Claim 4 — replace the delivering-round description to make the suffix explicit.**

> A round consists of a pre-list, `recover`, and a post-list. At least one round's post-list has the form `nd ++ [bankProcess k] ++ rest`, where `nd` contains no drop operation and `rest` is an arbitrary legal suffix.

**Claim 1 — clarify the executer identity.**

> The designated honest step is `execute c k` for any caller identity `c`; this model's execute transition ignores that identity. It does not require `c` to be the requester.

**Claim 3 — optionally spell out all of `Good`.**

> Every bank entry corresponds to an existing reserved request with exactly the same payload and an exact approval by a non-requester approver; bank keys are unique and the total is within the cap.

**Claim 6 — clarify how new tags and duplicates differ.**

> A new transmission produced by `transmit` or `recover` receives a fresh tag. Network duplication preserves the tag, and a drop removes one occurrence. Per-copy delivery requires an occurrence with the chosen tag to remain available at the indexed bank-processing step.

No English input or part file was edited; these replacements are proposals confined to this report.

## Ambiguities exposed

1. **“Strictly weaker” needs an implication domain.** A syntactic round predicate and a state-dependent fresh-copy predicate are not automatically comparable. Both separations are witnessed here; additional restrictions would be needed for an implication theorem.
2. **“Delivers” does not identify a new physical retransmission.** It describes a drop-free prefix and a bank-processing operation. A key may already have been paid or the recovery may emit nothing. Claim 6 explicitly requires a fresh recovery-batch copy, while claim 4 does not.
3. **“Before being dropped” means before all occurrences of the tag are lost.** A duplicated occurrence may survive even after another occurrence with the same tag is dropped. Tags name transmission lineages, not distinct identifiers for every network duplicate.
4. **“Honest execute” adds no caller check.** Claim 1's theorem quantifies the caller freely, and the transition ignores it. The English should not imply requester-only execution.
5. **“After any legal continuation” is universal quantification.** Orig exposes the continuation as a theorem parameter; Back quantifies it inside the conclusion. The gated projection and append identities establish the same pointwise family, including the empty continuation.
6. **“Exactly once” concerns the final ledger's key count.** Claims 2, 4 and 6 do not assert exactly one transmission, bank-processing attempt, acknowledgment or invocation. Claims 2 and 6 also do not state payload equality in their own conclusions.

No claim is unfinished or UNDECIDED. The English's auxiliary strict-weakening assertion is corrected rather than hidden by the six principal-theorem equivalence verdicts.
