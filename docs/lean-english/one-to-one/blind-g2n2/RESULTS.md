# Blind g2n2 Phase B results

All eight Phase A back hashes matched. All eight back files compiled **as written**, with exit code 0. No typing or syntax repairs were necessary. The typed copies are byte-identical, and [typed/HASHES.json](typed/HASHES.json) was written at **2026-10-13 04:29:51 UTC, before opening any original declaration**. [Original signatures](original-signatures.txt) were read afterward.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — SC12.no_fire_after_end | EQUIVALENT | [claim](bg2n2_1.receipt.json), [witness](bg2n2_1.witness.receipt.json) | Same lineage-filtered log equality; explicit `decide` matches Lean's Boolean coercion. |
| 2 — SC12.halt_freezes | EQUIVALENT | [claim](bg2n2_2.receipt.json), [witness](bg2n2_2.witness.receipt.json) | Same whole-state equality, under the same halted hypothesis. |
| 3 — sc12_safe_authenticated | EQUIVALENT | [claim](bg2n2_3.receipt.json), [witness](bg2n2_3.witness.receipt.json) | Eliminating the original's existential operation variable and rearranging conjuncts gives exactly the back conclusion. Both runs start at SC12.init. |
| 4 — forged12_spawns_without_auth | ENGLISH_STRONGER | [claim](bg2n2_4.receipt.json), [witness](bg2n2_4.witness.receipt.json) | Output-predicate comparison: back requires guarded = init; original requires guarded.live = []. The fixed example satisfies both; see the qualification below. |
| 5 — AuditDispatch.trace_safe | EQUIVALENT | [claim](bg2n2_5.receipt.json), [witness](bg2n2_5.witness.receipt.json) | Same invariant preservation and audit-prefix relation. No temporal write order in either conclusion. |
| 6 — AuditDispatch.app_cannot_effect | EQUIVALENT | [claim](bg2n2_6.receipt.json), [witness](bg2n2_6.witness.receipt.json) | Same effect-list equality for every non-dispatch operation; arbitrary starting state. |
| 7 — SC14.sc14_safe | EQUIVALENT | [claim](bg2n2_7.receipt.json), [witness](bg2n2_7.witness.receipt.json) | Same Good predicate from init under the same rollback-free trace hypothesis. |
| 8 — SC14.halt_freezes | EQUIVALENT | [claim](bg2n2_8.receipt.json), [witness](bg2n2_8.witness.receipt.json) | Same usage-list equality; rollback remains permitted. |

All listed claim and witness receipts pass. Witnesses are gated separately, with their own nonce and final axiom report. The allowed axioms remain exactly propext, Classical.choice, and Quot.sound; no other axiom was accepted.

## Pointwise comparison and scope

Each saved statement contains `FrozenBack`, copied from its hashed typed file, and `BackAt`/`OrigAt`, which spell out the respective conclusions. A definitional-equality example in each proof checks that re-quantifying `BackAt` recovers `FrozenBack`. A separate typed example checks the original declaration against `OrigAt`. These signature checks do not prove the equivalence: the `claim` proofs compare the conclusion predicates directly and do not invoke the eight original theorems to establish equivalence.

1. **Claim 1:** for the same admins, state, session and trace, under `Inv s` and `sess ∈ s.ended`, `BackAt ↔ OrigAt` is reflexive. Only the explicit Boolean coercion differs. The witness begins with an invariant state containing a recorded firing of the ended lineage and then admits a firing of another lineage. Thus neither an empty earlier log nor a frozen entire firing log is being asserted.
2. **Claim 2:** for the same admins, state and trace, under `s.halted = true`, both conclusions are `run admins full s ops = s`. Its witness has a nonempty earlier firing log and a nonempty continuation attempting further operations.
3. **Claim 3:** for **any** admins, U, issuer-operation trace and observation state s, the two safety/provenance predicates are equivalent. Back's witness `c` becomes Orig's witnesses `c, start c e.origin`; in reverse, the equality on Orig's witness operation permits substitution. This proof works even without the disjointness hypothesis, so it applies under the identical disjointness hypothesis and identical authenticated run used by both declarations. The non-vacuity witness uses admin 9 and U = [1], with a successful authenticated start followed by issuer-1 spawn and fire operations.
4. **Claim 4:** this theorem has a fixed trace and no free input parameters. To avoid equating two closed true propositions merely because both are provable, the comparison lifts their returned states to observation variables `unguarded, guarded`. Back's predicate is `unguarded.live.length = 2 ∧ guarded = SC12.init`; Orig's is `unguarded.live.length = 2 ∧ guarded.live = []`. The gate certifies Back → Orig and an observation-level counterexample to the converse: use an unguarded state with two live entities, and `guarded = { SC12.init with halted := true }`. The live list is empty, but that guarded state is not init. **This counterexample is not claimed reachable by forged12.** The separately gated Witness evaluates precisely the specified fixed trace and confirms that its actual guarded result *is* init. `ENGLISH_STRONGER` here records the stronger output contract, not a false English description of the concrete execution. No verdict is being inferred from the tautological equivalence of two closed true theorems.
5. **Claim 5:** for the same arbitrary starting state and trace, under `Inv s`, both conclusions are the identical conjunction of final `Inv` and the audit-prefix relation. Expanding `Inv` gives effect-id membership in audits and effect-list Nodup. Its witness retains effect 1, admits effect 2, and attempts a duplicate dispatch, with app operations, crash and restart interleaved.
6. **Claim 6:** for the same arbitrary state and operation, under `∀ id, o ≠ dispatch id`, both conclusions are the identical effect-list equality. The witness has an existing effect and an app request that changes requests while leaving effects intact.
7. **Claim 7:** for the same environment, initial expiry and trace, under `∀ o ∈ ops, legal o`, both conclusions are identical `Good E (run E full (init exp) ops)`. `Good` expands to componentwise cumulative bounds, componentwise bounds for every logical-clock window, and a per-record clock-before-recorded-expiry condition. The witness admits nonzero actual usage in two windows even though reported usage is zero.
8. **Claim 8:** for the same environment, state and arbitrary trace, under `s.halted = true`, both conclusions are identical usage-list equalities. The witness has nonzero pre-halt usage and spent counters; a rollback resets spent to zero, while attempted work and other operations leave usage unchanged.

## Hostile reading of “Does NOT say”

| Claim | Are the exclusions respected? |
|---|---|
| 1 | Yes, all three. Earlier firings can remain; only model entities are covered; there is no guarantee that a halt occurs. The witness also shows other lineages can fire. |
| 2 | Yes, all three. The conclusion concerns a supplied halted model state. Real revocation effectiveness is an external deployment condition, not a Lean hypothesis of this theorem. |
| 3 | Yes, all three. Platform issuer authenticity is outside Lean; spawn/bypass/fire claim no identity; exclusion from U follows from admin membership and disjointness. The witness admits issuer-1 spawn/fire operations. |
| 4 | Yes, all three. Neither conclusion quantifies over other attacks or provides platform authentication. The back adds whole-state equality for this example. |
| 5 | The three scope exclusions are respected. However, the parenthetical attribution of temporal ordering to dispatch_audit_first needs correction: that lemma only gives the two append equalities. Database privileges and real workflow exclusivity remain outside this theorem. |
| 6 | Yes, all three. No role/issuer check controls dispatch in this model; requests can choose eligible ids; effects refer to the modeled list. |
| 7 | Yes, all three. The usage labels do not authenticate meters, logical windows do not measure elapsed wall-clock time, and a caller number in an expiry operation is only a claimed identity. Refused work has no modeled consumption. |
| 8 | Yes, all three. Only usage is frozen; the rollback witness explicitly changes spent. Neither processing a halt nor stopping real running work follows. |

## Corrections to the English

**Claim 3 — specify the start state.** Replace the opening sentence with:

> Starting from SC12.init (empty active, ended, live and firing lists, and not halted), run the SC-12 model with each operation carrying an issuer number; apply an identity-claiming operation only when its claimed identity equals that number, and otherwise drop it.

Keep the existing safety and admin-issued-start conclusions and the stated disjointness hypothesis.

**Claim 4 — match the original's observed output.** Replace its Says sentence with:

> With admin list [9], full checks and initial state SC12.init, run the fixed trace in which issuer 1 requests start 9 5 and then spawn 5 6 true 0. With the authentication claim function constantly none, the final live list has length two. With claim12, the final live list is empty.

The whole-state equality in the back is also true for this trace, as the gated Witness shows, but it is stronger than the original's live-list conclusion. If John wants to retain “both operations do nothing,” identify it as an additional fact about this concrete run rather than the exact stated conclusion of forged12_spawns_without_auth.

**Claim 5 — remove the temporal attribution.** Replace Does NOT say (1) with:

> This theorem does not express the temporal order of database writes: it states that every final effect id appears in the audit list. The separate lemma dispatch_audit_first says that an enabled dispatch appends the audit id and the effect id in the same model step; its two list equalities do not themselves express a before/after time relation.

## Ambiguities exposed

- **Initial state in claim 3:** the blind back author explicitly flagged this before seeing the originals. Referring to sc12_safe suggests init, but naming init removes the ambiguity. Arbitrary starting states would need safety and provenance assumptions; neither compared declaration uses such a start state.
- **“Do nothing” in claim 4:** this can mean unchanged whole state or only no live entities at the end. The back selects the former; the original states the latter. The observation-level strength verdict must not be misread as a counterexample on the actual fixed trace.
- **“No operation claims any identity” in claim 4:** the unguarded claim function is constantly none; the embedded caller 9 in start 9 5 remains present and is used by SC12.step. This is not removal of the operation's caller field.
- **“Audit first” in claim 5:** both trace_safe and dispatch_audit_first operate on atomic state transitions and lists. Their names/comments cannot supply an absent temporal-write relation.
- **External “premises”:** registry completeness, effective revocation, authentic issuer numbers, a trusted meter/clock, credential separation, and database privileges are deployment obligations. They must not be mistaken for additional hypotheses checked by these Lean declarations. The rollback exclusion in claim 7, by contrast, is an actual Lean hypothesis.

## Gate and reproduction

[run_gate_blind.py](run_gate_blind.py) is the supplied wrapper relocated into this directory, with the bg2n2 file glob and project imports extended. Its output-location line also adjusts the derived project root for the extra directory level. [The exact diff](run_gate_blind.diff) records these path/import/glob changes. [leangate_imports.py](leangate_imports.py) is a byte-identical copy of the allowed gate helper; [gate-provenance.json](gate-provenance.json) records the matching hashes. No banned-token or axiom checks were changed.

From the repository root, run:

```bash
python3 docs/lean-english/one-to-one/blind-g2n2/regate.py
```

The script checks the saved statements, gates `claim` and `witness` separately for every id, replaces only their JSON receipts, and returns nonzero for any missing input, failed statement check or failed proof gate. It does not regenerate Lean inputs or consult old receipts. Temporary gate files are removed by the unchanged helper. The clean-state check removes current receipts and gate scratch before running, then checks the non-receipt files for changes; see [clean-regate-verification.json](clean-regate-verification.json).

The first run rejected comparison-proof elaboration errors for claims 4 and 5. Claim 4 needed explicit unfolding before decide; claim 5 needed qualification of AuditDispatch.Inv in simp. These were repairs to Phase B proof scripts, not to the back files. Archived attempts are retained in gate-attempts/; only the root-level receipts certify the final saved proofs.
