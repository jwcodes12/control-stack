# Blind G1a — Phase B results

All nine frozen back statements are **EQUIVALENT** to their original declarations by the comparisons described below. All nine comparison gates and all nine separately targeted Witness gates passed. These verdicts compare the Lean back statements with the original theorem statements; they do not certify every explanatory sentence in the English or any deployment assumption. Claim 4 has an incorrect exclusion, and claim 9 needs an accounting clarification.

| Claim | Verdict | Receipts | Note |
| --- | --- | --- | --- |
| 1 — `EgressGate.step_safe` | EQUIVALENT | [claim](bg1a_1.receipt.json), [Witness](bg1a_1.witness-receipt.json) | Same policy, state, action and invariant hypothesis; identical post-step conclusion. |
| 2 — `EgressGate.trace_safe` | EQUIVALENT | [claim](bg1a_2.receipt.json), [Witness](bg1a_2.witness-receipt.json) | Same policy, start, finite trace and invariant hypothesis; identical final invariant. |
| 3 — `SC05.cap_does_not_prevent` | EQUIVALENT | [claim](bg1a_3.receipt.json), [Witness](bg1a_3.witness-receipt.json) | Deterministic functions versus normalized probabilistic rows: pointwise embedding and support-preserving extraction both proved. |
| 4 — `SC05.zero_dependence_is_blind` | EQUIVALENT | [claim](bg1a_4.receipt.json), [Witness](bg1a_4.witness-receipt.json) | Same finite types, distributions and conclusion. The English's “not about … a bit” exclusion is wrong. |
| 5 — `SC05.forbidden_never_executes` | EQUIVALENT | [claim](bg1a_5.receipt.json), [Witness](bg1a_5.witness-receipt.json) | Same forbidden list and requests; same membership exclusion on the gate's executed list. |
| 6 — `SC06.sc06_safe` | EQUIVALENT | [claim](bg1a_6.receipt.json), [Witness](bg1a_6.witness-receipt.json) | Same policy and trace, `full`, `init`, and `Good`; label and confirmation caveats are accurate. |
| 7 — `SC06.halt_freezes` | EQUIVALENT | [claim](bg1a_7.receipt.json), [Witness](bg1a_7.witness-receipt.json) | Same arbitrary starting state with `halted = true`; equality of the whole state. |
| 8 — `SC07Liveness.sc07_safe` | EQUIVALENT | [claim](bg1a_8.receipt.json), [Witness](bg1a_8.witness-receipt.json) | Same environment and trace; the back's let-bound state unfolds to the original conclusion. Per-window bound is inclusive. |
| 9 — `SC07Refinement.concrete_safe` | EQUIVALENT | [claim](bg1a_9.receipt.json), [Witness](bg1a_9.witness-receipt.json) | Same configuration, quota-rule hypothesis and trace; same allowlist and natural-number `Q - 1` bound. Quota accounting occurs only after halt and allowlist filtering. |

## Evidence and comparison method

The nine original back files compiled untouched with `lake env lean`. Their SHA-256 values matched [the Phase-A manifest](back/BACK-HASHES.json). [Compile status](compile-logs/STATUS.json) records exit code zero for every file; individual logs are in `compile-logs/`. No typing or syntax repairs were needed. `compile-fixes/1.diff` through `9.diff` record that fact. The [typed hash manifest](typed/HASHES.json) was written before any original declaration was opened; all typed copies remain byte-identical to the hashed back files.

[Original signatures](ORIGINAL-SIGNATURES.json) records the inspected source locations, signatures and module hashes. Each statement file contains the back definition copied from its frozen typed file, followed by its comparison proposition. Each proof checks an `originalSignature` against the named original declaration. This checks the transcription's type; the comparison itself does not establish an iff by invoking two already-proved closed theorems.

For claims 1, 2, 4–9, `Claim` includes both a definitional equality tying the frozen back definition to its quantified `BackAt` conclusion and an iff between `BackAt` and `OrigAt` for the same inputs under the same hypotheses. The pointwise iff is definitional. For claim 9 only the order of the trace and quota-rule hypothesis is rearranged to match the back statement.

For claim 3, [the comparison statement](bg1a_3.statement.lean) and [proof](bg1a_3.proof.lean) establish a more substantial bridge:

- For **every** deterministic sender and decoder, the back success equality is iff the original predicate on their point-mass rows. Normalization is proved, not assumed away.
- For **every** original pair of normalized probabilistic rows with success 1, the proof selects an output of positive encoder probability for each bit on which that original decoder assigns probability 1 to the correct bit. Those outputs must differ. It constructs a deterministic decoder recovering both bits and proves its success is 1.
- The existential iff is then derived from those witness transformations. The reverse conversion is tied to the supplied probabilistic rows, rather than producing a fixed code independently of them.

Witnesses are nondegenerate: active egress with a recorded allowed request (1–2); distinct output codes recovering both bits (3); genuinely normalized seed/output/decoder laws and blind success 1/2 on Bool (4); both an accepted request and a refused forbidden one, with an ungated control (5); a cross-agent sensitive action with exact confirmation (6); a halted state with existing context and subsequent operations (7); two windows each forwarding five units, ten in total (8); forwarding plus quota and destination drops (9).

The deterministic [gate helper](leangate_imports.py) is byte-identical to the permitted helper. [The copied runner](run_gate_blind.py) changes exactly the output directory, statement glob and `PL_IMPORTS`; see [its diff](run_gate_blind.diff). Banned-token scanning, nonce assembly, kernel checking and the standard-axiom allowlist are unchanged. Each receipt includes the actual imports, project path and statement/proof/helper hashes; `*.gate.txt` and `*.witness-gate.txt` contain the separate nonce-bearing axiom reports. Final axiom reports use only `propext`, `Classical.choice` and/or `Quot.sound`.

Run `python3 docs/lean-english/one-to-one/blind-g1a/gate_all.py` from the repository root to reproduce both targets. This driver executes the copied runner using the original runner's location as `__file__`, preserving its unchanged `ROOT` calculation despite the copy's extra directory depth. It uses the copied, hash-checked helper. The inherited receipt field `gate_unmodified: false` refers to the adapted runner; `gate_byte_identical_to_helper: true` records the unchanged deterministic helper.

Earlier failed gate attempts are preserved in `attempts/`. The first failure was an unavailable umbrella `Mathlib.olean`; switching the permitted header to the already-built `Mathlib.Tactic` required no build or download. Subsequent failures concerned proof namespace resolution, unfolding the Witness before `decide`, and a simplifier recursion issue. None was a change to a back file or to the gate's security checks. The final top-level receipts supersede those attempts. Final receipt hashes were checked against all current statement and proof files.

## Hostile reading of “Does NOT say”

| Claim | Exclusions respected? | Assessment |
| --- | --- | --- |
| 1 | Yes — (a), (b), (c) | Topology flags are inputs; no Linux correspondence is established. Peers are only pinned, not semantically harmless. Existing safe starts are required, and the original module has no named initial-state witness. Phase B's new witness does not change that fact about the original. |
| 2 | Yes — (a), (b), (c) | Guards define direct attempts to be inert in invariant states; no real bypass exclusion is proved. “Authorised” is exactly gateway-origin and policy membership. |
| 3 | Yes — (a), (b), (c) | The theorem supplies a model code, not real agents or an executed harmful action. It is a no-go example for a cardinality cap. |
| 4 | Partly — (a), (c) yes; (b) needs correction | No real independence is proved, and dependent encoders are outside this equality. But `M = Bool` is permitted: a uniform bit has blind rate 1/2, as the gated Witness explicitly demonstrates. Nonuniform secrets are outside the stated success definition. |
| 5 | Yes — (a), (b), (c) | The forbidden set is externally chosen; only modeled action requests are mediated. Communication and alternative harmful actions are not prohibited. The gate's construction supplies the exclusion. |
| 6 | Yes — (a), (b), (c) | Caller ids are unchecked input numbers beyond list membership. Typed values are arbitrary naturals. `ctxOf` chooses the first matching context entry, and confirmations remain reusable. The theorem's `Good` uses the action's recorded `fromOther` label, not all historical origins of a value. |
| 7 | Yes — (a), (b), (c) | No halt occurrence or timing is promised. Halt is atomic in the model. Admin authentication is outside the numeric membership check. The freeze conclusion covers arbitrary halted states. |
| 8 | Yes — (a), (b), (c) | Ticks renew the per-window quota. Size is the explicit payload field; destination, event count, ordering and timing are not charged. A zero-size allowed send may be logged. This safety conclusion does not itself state a halt guarantee. |
| 9 | Yes — (a), (b), (c) | Resets renew windows; total payload across resets is unbounded by one `Q - 1`. Installation and kernel fidelity remain external. The conclusion counts forwarded upload payload, not return traffic or channel information; `Q = 0` gives bound zero and drops every packet reaching the quota rule. |

Assertions about named world-assumption registries, one-host testing and runtime evidence were not independently checked: the allowed English batch reports them, and source comments identify relevant correspondence obligations, but this run did not inspect the excluded documentation or deployment evidence.

## Corrections to the English

**Claim 4 — replace “Does NOT say” (b):**

> It applies to a uniformly random secret in any finite secret alphabet, including a bit, for which the blind success rate is 1/2. It does not give the same blind rate for a nonuniform secret, and it does not model whether a decoded value causes an action to execute.

**Claim 9 — replace the accounting description in “Says”:**

> In the concrete forward-chain model, a halted packet is dropped first and a packet to a non-allowlisted (ip, port) is dropped next. With the quota rule present, each remaining packet adds payload plus header bytes to `consumed`, even if the packet is then dropped because the updated counter is at least Q. From the initial state, after any packet, reset and halt trace, every forwarded packet targets an allowlisted (ip, port), and each window's forwarded payload is at most the natural-number quantity Q - 1.

This removes the possible reading that denied or halted packets consume quota. Those branches update drop counters without incrementing `consumed`.

**Claim 3 — sharpen the first two sentences of “Says”:**

> With one freely chosen output from an alphabet of 65536 values and identity observation, there are a deterministic sender and decoder that recover a uniform secret bit with probability 1. The original theorem permits normalized probabilistic encoder and decoder rows; a deterministic code suffices, so this alphabet-size cap does not preclude conveying a bit.

This identifies the cardinality model without suggesting that Lean models a real wire encoding or repeated-message budget.

## Ambiguities exposed

1. **“Distribution” versus deterministic functions (claim 3).** The back omits explicit distribution hypotheses because its rows are point masses. This is valid only after showing normalization and that perfect probabilistic witnesses can be converted to deterministic ones. The gated support-preserving extraction supplies that bridge; it does not equate arbitrary randomized rows with arbitrary deterministic rows.
2. **A bit is still a uniform secret (claim 4).** The incorrect exclusion is an English problem even though the frozen back matches the original. The model also treats the secret as uniform independently of the seed law; an arbitrary seed law is not a law allowed to reveal a secret through secret-dependent conditioning.
3. **Historical origin versus selected label (claim 6).** A value read from another agent at some point need not make the action's first matching entry `fromOther = true`. The batch correctly makes this distinction explicit. “Confirmed by a user” means numeric list membership, and a confirmation can authorize multiple matching actions.
4. **Finite alphabet versus numeric fields (claims 3 and 6).** `Fin 65536` is a cardinality restriction; SC06's typed fields are unrestricted naturals. The SC06 theorem does not supply a finite covert-channel capacity bound.
5. **Whole execution versus each quota window (claims 8–9).** Quota renewal is an arbitrary operation in both models. Witness 8 forwards ten units under quota five, in two windows. The abstract send guard admits a total equal to `q`; the concrete rule drops a packet reaching `Q` after on-wire accounting, giving forwarded payload at most `Q - 1`.
6. **Halt freezes which state? (claims 7 and 9).** SC06 freezes the entire state. In the concrete SC07 model, post-halt packets may increase `haltDrop` and a reset may clear `consumed`; the separate forwarding-freeze theorem concerns the forwarded log. Claim 9 does not assert whole-state freezing.
7. **Final state versus all prefixes (claims 2, 6, 8–9).** Their formal conclusions concern the final state of any finite trace. Applying them to each finite prefix justifies “always” within that model. This adds no statement about real-time concurrency, in-flight traffic or deployment fidelity.
