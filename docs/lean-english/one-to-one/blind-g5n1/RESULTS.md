# Blind Phase B: batch g5n1

All ten Phase A files compiled as written. Their original hashes matched `back/BACK-HASHES.json`; no compile repairs were needed. Byte-identical copies and `typed/HASHES.json` were saved at **2026-10-13 05:12:39 UTC, before any original declaration was opened**. Each `compile-fixes/<n>.diff` records that no repair occurred. No original project source or English input was edited.

The table compares the frozen Back formalization with the original declaration. English correspondence problems are reported separately below; a matching Back and original does not certify every informal interpretation of the English.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 `sc21_safe` | EQUIVALENT | [claim](bg5n1_1.receipt.json), [witness](bg5n1_1.witness.receipt.json) | Same published-snapshot predicate, for the same environment and trace. |
| 2 `sc21_undetected_prob` | EQUIVALENT | [claim](bg5n1_2.receipt.json), [witness](bg5n1_2.witness.receipt.json) | Same exact ratio and cardinality premise; probability language needs feasible samples. |
| 3 `sc21_undetected_le_pow` | EQUIVALENT | [claim](bg5n1_3.receipt.json), [witness](bg5n1_3.witness.receipt.json) | Natural subtraction in Back equals real subtraction in Orig under `B ≤ N`. |
| 4 `observable_sample_nogo` | EQUIVALENT | [claim](bg5n1_4.receipt.json), [witness](bg5n1_4.witness.receipt.json) | Same existential corrupted set, cardinality, disjointness, and survival 1. |
| 5 `sc21_adaptive` | EQUIVALENT | [claim](bg5n1_5.receipt.json), [witness](bg5n1_5.witness.receipt.json) | Sum over the sample family equals the original all-set sum with zero weights elsewhere. |
| 6 `sc21_adaptive_content` | EQUIVALENT | [claim](bg5n1_6.receipt.json), [witness](bg5n1_6.witness.receipt.json) | Product-type kernel sums and schedule weights normalize exactly; both quantify over finite hidden types. |
| 7 `sc21_adaptive_recall` | ENGLISH_WEAKER | [claim](bg5n1_7.receipt.json), [witness](bg5n1_7.witness.receipt.json) | Orig → Back by restricting the rule's domain. Back adds a nonredundant full-choice marginal premise. Conclusions are equivalent on the common domain. |
| 8 `sc22_unreplicated_misreport` | EQUIVALENT | [claim](bg5n1_8.receipt.json), [witness](bg5n1_8.witness.receipt.json) | Same ratio and corruption predicate as claim 2. |
| 9 `sc23_safe` | EQUIVALENT | [claim](bg5n1_9.receipt.json), [witness](bg5n1_9.witness.receipt.json) | Same `Good`: exact user confirmation for sensitive provenance-true actions, plus distinct used nonces. |
| 10 `halt_freezes` | EQUIVALENT | [claim](bg5n1_10.receipt.json), [witness](bg5n1_10.witness.receipt.json) | Same equality for arbitrary halted starting states and arbitrary further traces. |

Each claim receipt and each separately targeted witness receipt passed the deterministic gate. The gate's banned-token scan, nonce-based final theorem, and axiom allowlist are unchanged. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the certified proofs. The receipt contains the complete statement-check and gate logs, source hashes, project path, and trusted imports. Development failures are retained separately under `development-gate-logs/`; they are not final receipts.

The statement files contain the compiled Back definition verbatim, with its enclosing namespace relocated to `PL_bg5n1_<n>`, and separate `HBack`, `HOrig`, `BackAt`, and `OrigAt` definitions. Every claim proves that the copied Back definition is precisely its extracted schema. For equivalent claims it additionally proves hypothesis equivalence and conclusion iff at the same parameters under `HBack`. The `original_type` helper applies the actual original declaration to `HOrig` to type-check the transcription of its signature. It is **not used** to establish any comparison iff. Original signatures are saved in [ORIGINAL-SIGNATURES.md](ORIGINAL-SIGNATURES.md).

For claim 7, “weaker” describes theorem coverage: stronger premises restrict the kernels covered by the same conclusion. Its gated claim proves `HBack → HOrig`, the pointwise conclusion iff, and the transformation `(HOrig → OrigAt) → (HBack → BackAt)` using an arbitrary supplied local rule. It also proves a concrete `HOrig ∧ ¬HBack` certificate, refuting reverse premise conversion. It does not assert a false numerical conclusion or mathematical nonimplication between two already-proved closed theorems.

The strictness certificate uses `N=2`, `B=k=1`, `r=1/2`, finite hidden type `Unit`, a reference rule choosing “not corrupt” with probability 1, and a normalized kernel assigning probability 1 to “corrupt and caught.” Its no-catch marginal is zero, so all original recall inequalities hold at every history. Its full corruption marginal is 1, exceeding the reference rule's corruption probability 0, so Back's added marginal premise fails. This difference concerns caught-path mass; it does not refute the original survival bound.

The witnesses are nondegenerate: claim 1 actually publishes two reports, re-executing one while leaving an incorrect value unchecked; claims 2, 3, and 8 have two results, one corrupt result, and a nonempty size-one sample family; claim 4 has a sampled finding and a distinct unsampled finding; claim 5 has positive probability for each choice; claims 6 and 7 have positive attack/no-catch mass, with claim 7 using `r=1/2`; claim 9 actually executes a sensitive tainted action with a user confirmation; claim 10 starts with stored values and an executed action and attempts further operations.

“Does NOT say” audit, claim by claim:

- **1:** All three exclusions are respected. `PubOk` checks digest numbers and truth only for recorded re-executed tasks. It neither forces sampling nor connects a supplied digest to executable code. The positive witness retains an unchecked wrong value in a published snapshot.
- **2:** All exclusions are respected: an exact fraction supplies no smallness guarantee, the corrupt set is a fixed parameter, and sampled corruption is detected perfectly by the disjointness event. Hiddenness is a deployment correspondence condition, not a theorem about an implementation's information flow.
- **3:** All exclusions are respected. The upper bound can be large; it concerns a fixed corrupt set and perfect detection. The natural/real subtraction change is harmless only because the shared premises include `B ≤ N`.
- **4:** Both exclusions are respected. The existential set depends on the known schedule; the theorem neither explains how the schedule leaks nor bounds a hidden schedule.
- **5:** All four exclusions are respected. The visible history is exactly the previous decision/catch outputs, with a `Unit` content slot; task order and deterministic catches are built into `hiddenK`. The theorem establishes neither real-world hiddenness nor a small numerical bound.
- **6:** Both exclusions are respected within the finite model. `successInd` explicitly requires disjointness and no catches. It does not require the kernel's catch bit to track sampled attacks faithfully; extra catches can reject paths. The marginal premise must be supplied, and no effective extra check is exhibited. An arbitrary kernel need not be related to a particular deployed checking system.
- **7:** The exclusions concerning the value of `r`, independence, harmlessness, and smallness are respected. The original uses per-history joint no-catch inequalities, without assuming independent detections. However, the affirmative “same kernel conditions” description adds a condition absent from the original, and the plain conditional-recall wording needs qualification as described below.
- **8:** All exclusions are respected. Reports and truth are natural numbers; numerical equality does not formalize scientific interpretation. The theorem provides neither a small bound nor coverage of adaptive misreporting or imperfect replication.
- **9:** All four exclusions are respected. `prov` is generated by operation rules, not an independently checked semantic dependency. Empty-source derivation permits arbitrary untainted content. `Good` covers sensitive provenance-true actions and does not validate confirmation wisdom, untainted content, or the caller of `userInput`. Confirmation identity here is its recorded nonce.
- **10:** All exclusions are respected. The theorem assumes an already halted state; it neither guarantees a halt nor undoes prior actions. Administrative identity is represented by list membership. Reachability through an authorized halt is not an additional theorem premise.

## Corrections to the English

**Claim 7 — replace the “same kernel conditions” passage:**

“Let the hidden component have a finite type. The kernel is nonnegative and has total mass at most 1 at every history for each allowed sample. A reference rule σ is a distribution at every visible history. Assume that the joint mass of choice a and no catch is at most σ(visible history)(a), multiplied by 1−r when the current round is sampled and a is corruption. Then the uniformly averaged probability mass of at least k corruptions and no catches is at most `hypMiss N B k r`. Unlike claim 6, this theorem requires no bound on the full choice marginal summed over both catch flags.”

**Claim 7 — replace the opening conditional-recall wording:**

“The recall assumption is the stated per-history joint no-catch mass inequality. Reading r as an actual conditional detection probability requires an additional correspondence between σ and the kernel's choice probabilities.”

The original constrains no-catch mass, so it allows arbitrary distributions of already-caught mass subject to the total-mass bound. Even Back's full-choice domination condition is an inequality, and the kernel is a subdistribution. These premises alone should not be described as an equality of the agent's actual choice law with σ.

**Claims 6 and 7 — specify the finite scope:**

“Each round may have an arbitrary hidden component drawn from a finite type; histories are lists of such components and visible outputs.”

Both original declarations and both Back files require `[Fintype Y]` with `Y : Type`. Infinite hidden alphabets and other universes are not covered by these declarations. The Phase A comments flag this limitation, but the supplied finite formalizations are compilable and comparable; this is not a failure to formalize their actual finite statements.

**Claims 2 and 8 — qualify the probability interpretation:**

“For `B ≤ N`, choose a sample uniformly from all size-B subsets of the N results. The probability that it misses the fixed k corrupted results is exactly `C(N−k,B)/C(N,B)`. The Lean counting-ratio identity also holds for `B > N`, where the sample family is empty and real division makes the ratio zero; that case is not a uniform sampling probability.”

These are proposed replacement sentences only. No English part file was edited.

## Ambiguities exposed

1. **No sample exists for `B > N`.** Claims 2 and 8 omit `B ≤ N`. Their mathematical ratio is totalized, while their probability wording presupposes a nonempty family. The frozen Back explicitly chooses the ratio interpretation and matches the original.
2. **“Arbitrary hidden component” omits finite scope.** Claims 6 and 7 quantify over every finite hidden type, not every type. Arbitrarily long histories do not remove this alphabet restriction.
3. **Joint no-catch domination versus full-choice law and conditional recall.** Claim 7's original needs only the joint bound, while the English and Back inherit full-choice domination from claim 6. Its “whenever corrupted and sampled” wording can also suggest conditional recall beyond the literal joint inequality. The strict hypothesis discrepancy is gate-certified.
4. **Semantic truth versus model fields.** Claim 1's digest is a supplied number; claim 9's provenance is computed from listed sources. Their “Does NOT say” sections correctly acknowledge these distinctions, and neither comparison closes those deployment gaps.
5. **The provenance of the halt flag.** Claim 10's operational description says authorized halt sets the bit, but its theorem needs only the bit's value and holds for arbitrary starting states, including states not shown reachable from `init`.

To reproduce all checks from the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g5n1/regate.py
```

The script reads saved statement/proof files, verifies their frozen hashes, runs the unchanged deterministic gate on both `claim` and `witness`, writes only JSON receipts plus transient gate files, and exits nonzero on any failure. It needs no prior receipts or gate directory. `run_gate_blind.py` retains the original wrapper's checks; relocation requires correcting its project-root parent index and helper lookup in addition to the requested imports/glob settings. The exact wrapper diff is saved in [run_gate_blind.diff](run_gate_blind.diff); the gate implementation itself was not copied or edited.
