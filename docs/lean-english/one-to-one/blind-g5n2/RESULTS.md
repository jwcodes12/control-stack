# Blind g5n2 — Phase B

**All twelve frozen mathematical back translations are EQUIVALENT to the original theorem statements**, with the scope clarifications for claims 11 and 12 below. Every saved `Claim` and every saved `Witness` passed the deterministic gate separately. This verdict concerns Back ↔ Orig; it does **not** certify every explanatory sentence in the English. In particular, the bits gloss in claim 11 and the probability interpretation in claim 12 need correction.

All twelve back files compiled as written and matched `back/BACK-HASHES.json`. The identical typed copies and `typed/HASHES.json` were written at **2026-10-13 05:13:08.885759 UTC**, before any original declarations were opened. Each `compile-fixes/<n>.diff` records that no repair was required. Originals were subsequently located in `ControlStack/`; their declaration types, locations and source hashes are saved in `originals/`.

The proof files establish equality of expressions, rearrange witnesses, or reduce theorem schemas using their assumed conclusions. They do not invoke the original theorem proofs to establish equivalence. Thus this is not an iff obtained by independently proving two closed true propositions. For the finite claims 2, 5 and 8, the two closed propositions are definitionally identical, rather than merely both true.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — `SC23Isolation.noninterference` | EQUIVALENT | [claim + witness](bg5n2_1.receipt.json) | Identical trace relation and four-field conclusion. Does NOT say exclusions respected; witness also shows executed logs can differ. |
| 2 — `SC23Isolation.w1_impossible` | EQUIVALENT | [claim + witness](bg5n2_2.receipt.json) | Same concrete conjunction after unfolding lets, including value 41. Exclusions respected; nonce 0 should be explicit. |
| 3 — `SC23Isolation.sc23_isolated_safe` | EQUIVALENT | [claim + witness](bg5n2_3.receipt.json) | Same per-action `ActOk`, including recorded action nonce. Exclusions respected; witness executes twice using one confirmation. |
| 4 — `SC23IsolationV2.noninterference_authed` | EQUIVALENT | [claim + witness](bg5n2_4.receipt.json) | Same issuer-preserving relation and authenticated-run conclusion. Exclusions respected; no executed-log or confirmation-log equality. |
| 5 — `SC23IsolationV2.w1_impossible_v2` | EQUIVALENT | [claim + witness](bg5n2_5.receipt.json) | Same concrete conjunction and value 0. Exclusions respected; nonce 0 should be explicit. |
| 6 — `SC23IsolationV2.sc23v2_safe_authenticated` | EQUIVALENT | [claim + witness](bg5n2_6.receipt.json) | Same existential issued confirmation, user membership and exclusion from U. Exclusions respected: no order or one-use conclusion. |
| 7 — `AuthInstances.sc23_safe_authenticated` | EQUIVALENT | [claim + witness](bg5n2_7.receipt.json) | Same `Good` and confirmation origins; explicit existential operation is eliminated by equality. Exclusions respected; user input is not issuer-authenticated here. |
| 8 — `AuthInstances.forged23_acts_without_auth` | EQUIVALENT | [claim + witness](bg5n2_8.receipt.json) | Definitionally identical forged-trace control: one action without authentication, none with it. Exclusions respected. |
| 9 — `MonitorCollusion.pass_transfer` | EQUIVALENT | [claim + witness](bg5n2_9.receipt.json) | Pointwise iff by absolute-difference symmetry. Exclusions respected; witness has TV = 1 and pass rates 1 and 0. |
| 10 — `MonitorCollusion.collusion_uniform` | EQUIVALENT | [claim + witness](bg5n2_10.receipt.json) | Boolean phase/action sums equal the back translation's two pass-rate terms. Exclusions respected; single-item uniform prior only. |
| 11 — `MonitorCollusion.canon_channel` | EQUIVALENT | [claim + witness](bg5n2_11.receipt.json) | Exact-decoding bound only. Pointwise per-seed iff plus singleton/averaging reduction certifies the added shared-seed scope. Bits gloss remains unformalised. |
| 12 — `MonitorCollusion.phase_learning` | EQUIVALENT | [claim + witness](bg5n2_12.receipt.json) | Same scalar bound; omitted certificate nonnegativity is bridged, including empty hidden-state types. Exclusions respected, but calling the scalar a probability needs kernel normalisation. |

For every row, the linked receipt contains the statement check, separate claim/witness gate logs, and hashes of the saved statement, proof and gate helper. The permitted axiom set is unchanged: `propext`, `Classical.choice`, `Quot.sound`. No failed gate is counted as certification.

## Pointwise comparisons and scope

1. With the same `E`, `ops`, `ops'` and `List.Forall₂ SameExceptContent` hypothesis, both conclusions are exactly `Rel (run E full init ops) (run E full init ops')`. `Rel` compares user inputs, planner values, quarantine length and halted status. The proof also connects the frozen Back definition to this parameterised schema by definitional equality.
2. Both propositions contain exactly the same injected/clean traces and the same two executed-log equalities. The back translation's lets introduce no extra hypothesis or freedom.
3. For the same environment, trace and executed action, Back ↔ Orig expands to the same sensitive/tainted implication and the same `∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, ...` conclusion. This requires the matching recorded nonce, tool, values and user caller; it does not require distinct nonces across executed actions.
4. Under the identical issuer/content relation, both conclusions are exactly the same `Rel` on authenticated runs. The opaque view is a check configuration, not a constraint on the arbitrary planner program beyond the provided view.
5. As in claim 2, the exact trace and both equalities are definitionally identical; the derived value is 0.
6. Fixing `E`, `U`, the disjointness hypothesis, issued trace and sensitive tainted executed action leaves exactly the same `∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, confirm c n x.tool x.vals) ∈ ops`. Neither side's conclusion identifies this existential nonce with `x.conf`, or gives a trace position. Stronger operational properties would require further proofs.
7. Fixing policy, U and issued trace preserves `Good` unchanged. For each final confirmation, the original's `∃ c o, ... ∧ o = confirm ...` is converted in both directions to the back translation's direct membership of that confirm operation. User membership, `c ∉ U` and `c = cf.by_` are merely reordered. `Good` includes provenance-based action safety and `Nodup` of recorded action-confirmation nonces.
8. Both closed propositions use the original concrete `forged23` trace and the same authenticated/all-none claim functions. The witness separately unfolds that trace and computes both outcomes.
9. For the same two laws and rule, substituting `Ph = P`, `Pr = Q` in the original leaves the back translation's bound with the absolute difference reversed. `abs_sub_comm` gives the iff without using either inequality as a true theorem.
10. Substituting `Ph = Q`, `Pr = P`, expanding the two Boolean sums and doing ring algebra gives precisely `(passRate P monitor_true + passRate Q monitor_false)/2`. The TV argument order and uniform prior match.
11. Holding a codebook fixed, collapsing the exact-recovery indicator in the original yields `card(M)⁻¹ * Σ_m Σ_v enc(m,v) * dec(canon(v),m)`, exactly the per-seed Back expression; multiplication by an inverse equals division. This pointwise identity holds even without distribution hypotheses. The back translation additionally quantifies over finite shared seeds: assuming the original bounds for each fixed seed, multiply each by its nonnegative seed probability and sum; conversely, specialise the seeded Back schema to `Unit` with mass 1. The saved proof certifies these two schema reductions, with the same per-seed distribution hypotheses. **It does not identify one averaged inequality with a conjunction of inequalities for every seed.** Seed independence from the uniform message is built into `successProb`.
12. The original phase sum and Back's two-term sum are pointwise identical by Boolean-sum expansion and ring algebra, under any fixed kernels, guess, L and m. The original additionally assumes `∀ g o, 0 ≤ c g o`. The saved schema reduction derives this from domination and kernel nonnegativity when Y is inhabited, by lifting any visible history with a fixed hidden value. If Y is empty, all positive-round values are zero; at m = 0, the guess distribution gives 1/2. This covers the extra Back scope without assuming the original theorem's truth. No kernel normalisation is introduced.

## Corrections to the English

**Claim 11 — replace the “i.e. ... bits” sentence:**

> For finite message and view sets, with a nonempty message set and a uniform message, the probability of exact decoding after the fixed K-class canonicalisation is at most K divided by the number of messages. This theorem states an exact-decoding bound; it does not define or prove a bound for an information measure in bits.

The log-K intuition can be discussed separately after specifying an information measure and proving the appropriate channel theorem. It is not a second formal conclusion of `canon_channel`, and is not logically synonymous with this single success-probability inequality.

**Claim 11 — make randomisation explicit if retaining the Back convention:**

> The encoder and decoder may share a finite random seed drawn independently of the uniform message. Conditional on each seed, each encoder and decoder row is a probability distribution. The bound holds after averaging over the seed; the original fixed-codebook theorem is its single-seed instance.

This replaces the ambiguous “fixed in advance, possibly randomised” wording and states the finite-view assumption omitted from the English.

**Claim 12 — replace the probability wording under the existing formal hypotheses:**

> For finite hidden-state and visible-output sets, nonnegative round kernels dominated at every history by a phase-independent certificate of mass at most L, with L nonnegative, give a uniform-prior correct-guess weighted mass at most L^m/2. If every round kernel is also a probability distribution, this weighted mass is the probability of a correct final guess.

The existing English explicitly notes that Lean imposes no kernel mass bound, but still repeatedly calls the formal scalar a probability. These statements need to be reconciled. The gated witness uses one hidden state, one output, a constant kernel and certificate of 3, L = 3, a uniform guess and m = 1. It satisfies even the original's nonnegativity premise, yet the formal correct-guess scalar is **3/2**, greater than 1. The inequality remains correct. Kernel normalisation is an extra assumption needed for the probability interpretation, not a repair to Back.

**Claims 2 and 5 — make the concrete operation explicit:**

> The action is `act 5 [1] 0`: sensitive tool 5, planner-value index 1, nonce 0.

Both back translations chose the original's nonce 0. The nonce choice is harmless for these untainted executions, but spelling it out removes an unnecessary choice in a one-to-one translation.

**Claim 2 — replace the parenthetical identification of general laundering impossibility with noninterference:**

> This finite computation does not prove a general anti-laundering result. The separate noninterference theorem shows that changing tool-result contents cannot change planner-visible state under its stated trace relation and isolation assumptions.

This preserves the causal guarantee without suggesting that every trusted value equal to injected content, every executed sensitive action, or every arbitrary planner behaviour is ruled out.

## Ambiguities exposed

- **Formal verdict versus prose gloss.** The table certifies the saved mathematical Back definitions. Claim 11 explicitly leaves the bits phrase outside its formal definition. That omitted phrase is unformalised here, despite the EQUIVALENT verdict for the exact-decoding bound.
- **Claim 11's finite alphabets and shared randomness.** The original needs finite M and V, a nonempty M, and a decidable equality on M for its indicator. Back obtains equality classically and adds finite shared randomness. The gate certifies the algebraic extension; it does not cover arbitrary infinite view laws, message-correlated seeds or side channels.
- **Claim 12's finite alphabets.** Both Lean formulations require finite Y and O. The English should say so. The empty-Y corner also explains why global certificate nonnegativity is not literally derivable from domination in every type, although the bound still follows.
- **Claim 12's certificate premise.** An explicit nonnegative certificate matches the original declaration most literally. The omission is mathematically harmless for the bound, as the gated reduction proves; it should not be described as a blanket equivalence of all hypothesis predicates.
- **Claims 1 and 4: “planner holds”.** Read this as the model's stated planner-visible fields. It excludes executed arguments, quarantine contents, confirmation logs and real runtime side channels. The claim-1 witness exhibits equal-structure traces with different execution outcomes: content 66 matches the common confirmation and executes, content 0 does not and is blocked.
- **Claim 3: confirmation reuse.** The gated witness executes the same tainted action twice after a single confirmation. Claim 7's first-model `Good` adds a distinct non-reuse property. The English correctly separates these models.
- **Claims 6 and 7: provenance versus ordering.** The conclusion establishes operation membership in the issued trace; it contains no index or prefix relation. The English correctly avoids presenting a temporal theorem. Authenticity of the platform-reported issuer and an informed UI remain world assumptions.
- **Claims 9 and 10: one decision, fixed laws.** The “Does NOT say” exclusions about side information, TV being small and multi-item success are respected. Their tight witnesses achieve perfect distinction at TV = 1, illustrating the permitted vacuous endpoint.
- **Claim 12: scheduling and deployment.** Re-randomising a phase before the bound becomes vacuous is external operational advice. No rotation schedule, runtime estimate of L or protection against a long reused phase is proved.

## Reproduction and protocol record

From the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g5n2/regate.py
```

This script rechecks all twelve statements and gates `claim` and `witness` separately for each, using the copied runner's imports and project path. It records both targets even if one fails and exits nonzero if any statement, claim or witness check fails. It reads saved statements/proofs and rewrites only receipt files; the unchanged gate creates and removes temporary Lean files inside `blind-g5n2/gate-tmp/`.

A clean-state run, after deleting existing receipts, temporary gate files and local Python caches, exited **0** with **12 statement checks, 12 claims and 12 witnesses passing**. The before/after file-hash comparison found no changed nonreceipt file and exactly twelve new receipts; see [REGATE-VALIDATION.json](REGATE-VALIDATION.json). Saved statement/proof hashes are in [CHECK-HASHES.json](CHECK-HASHES.json).

`leangate_imports.py` inside this directory is byte-for-byte identical to the allowed original helper. The runner's changes are output/project path relocation, project imports and the file glob; [run-gate-paths.diff](run-gate-paths.diff) records them. Its parent-depth change is necessary because the copied script lives one directory deeper. No banned-token or axiom check was modified. `regate.py` disables Python bytecode generation.

**Protocol deviation:** an early Python import automatically generated `docs/lean-english/one-to-one/__pycache__/leangate_imports.cpython-<version>.pyc` outside the authorised output directory at 05:16:53 UTC. That run-created cache was removed, the helper was copied inside the output directory, and bytecode generation was disabled for regating. No source outside the output directory was edited; no `ControlStack/` file was changed and no git command was run. The initial run therefore breached the strict output-only constraint through an automatic cache write; cleanup does not erase that historical deviation. The clean regate run stayed within the output directory. No excluded English document or previous comparison result was read.
