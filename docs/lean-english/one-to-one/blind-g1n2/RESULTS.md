# Blind g1n2 Phase B results

The frozen back statements match the original specifications for claims 1–9. Claim 10 has the same conclusion on a strictly larger hypothesis domain: its traffic certificate is a sub-distribution, whereas the original requires a distribution.

These are specification comparisons. EQUIVALENT requires equality of hypothesis domains and pointwise equivalence of conclusions; it does not follow from two closed statements being true. ENGLISH_STRONGER here means the same conclusion is asserted for more instances. The directional proof specializes Back to Orig, and the witness establishes strict domain inclusion. This does not assert that the original theorem and surrounding mathematics cannot independently prove the generalized bound.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 `sc01_case` | EQUIVALENT | [claim](bg1n2_1.receipt.json), [witness](bg1n2_1.witness.receipt.json) | All five conjuncts preserved. Reordered side premises and charge-membership/event-equality premises are equivalent. |
| 2 `core_bound` | EQUIVALENT | [claim](bg1n2_2.receipt.json), [witness](bg1n2_2.witness.receipt.json) | Pushing the trace law to final views gives exactly the original direct trace sum. Transition prose needs a before-close qualifier. |
| 3 `covert_bound_lifetime` | EQUIVALENT | [claim](bg1n2_3.receipt.json), [witness](bg1n2_3.witness.receipt.json) | Same tuple observation, distributions, and product/counting conclusion. |
| 4 `sc02_accumulated` | EQUIVALENT | [claim](bg1n2_4.receipt.json), [witness](bg1n2_4.witness.receipt.json) | Fin-indexed product equals range product; cardinality casts agree. Witness also proves admissible weighted success can equal 2. |
| 5 `rekey_epoch` | EQUIVALENT | [claim](bg1n2_5.receipt.json), [witness](bg1n2_5.witness.receipt.json) | Curried in-window premises and the disjunctive outside-window condition match the original conjunction/negation. |
| 6 `log_channel` | EQUIVALENT | [claim](bg1n2_6.receipt.json), [witness](bg1n2_6.witness.receipt.json) | Nested hidden/output sums equal the product-type sum. Parameter order is accounted for. |
| 7 `canonical_seq` | EQUIVALENT | [claim](bg1n2_7.receipt.json), [witness](bg1n2_7.witness.receipt.json) | Same sub-probability premises and fixed-length alphabet bound. The English wrongly excludes the one-shot instance. |
| 8 `windows_needed` | EQUIVALENT | [claim](bg1n2_8.receipt.json), [witness](bg1n2_8.witness.receipt.json) | Identical quota, total, and positive-quota premises and traffic-count conclusion. |
| 9 `sc07_mixed` | EQUIVALENT | [claim](bg1n2_9.receipt.json), [witness](bg1n2_9.witness.receipt.json) | IsDist expands to positivity plus sum 1; the paired catch premises and placement of multiplication inside the conditional agree. |
| 10 `sc07_fixed_budget` | ENGLISH_STRONGER | [claim](bg1n2_10.receipt.json), [witness](bg1n2_10.witness.receipt.json) | Back permits traffic-certificate row mass ≤ 1; Orig requires mass = 1. Same payoff and bound. Strict witness uses N=2, B=1, r=1/2, and sigma(g,a)=1/4, with row mass 1/2. A normalized original instance is also witnessed. |

The clean re-gate exited 0: all 10 claim gates and all 10 separately run witness gates passed. Final audit completed at 2026-10-13T05:36:30.854543+00:00; receipt/source hashes and the unchanged gate helper were verified in `FINAL-AUDIT.json`.

Each claim has a saved statement, claim proof, and separate witness proof. The statement-check and gate transcripts are beside its JSON receipts. Claims 2–9 explicitly prove `BackAt ↔ OrigAt` for every common parameter instance, together with hypothesis-domain equivalence and conclusion equivalence. Their gate also proves that these schemas reconstruct the entire frozen Back and copied original type. Claim 1 checks the components pointwise and assembles the full structural equivalence. Claim 10 gates `BackAt → OrigAt`, domain inclusion, conclusion identity, and specialization of the entire frozen Back to the original type. No comparison proof invokes the original theorem as a way to make both sides true.

All ten originals are theorem claims, so there is no definition claim requiring a separate definition-level iff.

## Corrections to the English

**Claim 2, transition description.** Replace the unqualified blanking sentence with: “Before the first close, a rejected payload, unknown channel, side action, or slot overflow blanks the episode. The first close freezes the delivered view; every later event leaves that snapshot unchanged. If no close occurs, the final view is delivered at the end of the trace.” The back statement uses `runG` and therefore already follows these transitions. This prose defect does not change the back/original verdict.

**Claim 3, independence wording.** Replace “the secret is uniform and independent of the seed and of the receiver's inputs” with: “The success expression averages over a uniform secret independently of the shared seed. The decoder receives the seed and the view tuple; that tuple may depend on the secret.” Independence from the receiver's actual observed tuple would be an extra and generally false condition.

**Claims 4–5, probability and kernel wording.** Replace the normalization explanation with: “Only non-negativity and certificate domination are required of the sender's kernel; its rows need not have mass at most one. The theorem bounds the stated weighted exact-recovery expression. When the kernel rows are probability or sub-probability laws, that expression has the corresponding probability interpretation.” For claim 4 the separately gated witness satisfies the actual premises with k=1, E=1, singleton hidden/visible alphabets, K=4, c=4, and L=4; a decoder always guessing zero yields weighted success 2. Thus saying only that the kernel ‘may lose mass’ misses that it may also gain mass.

**Claim 5, persistent state and the other rounds.** Replace the categorical cache claim with: “The bound includes all n rounds provided the same secret-independent certificate has mass at most one outside the window. Persistent hidden state violates this premise only when its effect on visible outputs prevents such a certificate; hidden correlation by itself does not force a violation.” Replace “whatever happens in the other rounds” with “for any other-round kernels satisfying the outside-window domination and mass premises.” A mass-one certificate rules out distinct certain visible outputs for two secrets; it should not be described as forbidding every possible conditional or partial disclosure in a sub-probability model.

**Claim 6, free-text qualification.** Replace “if a free-text field exists the bound is void” with: “A visible field outside the stated finite record alphabet must be counted or certified separately. A field large enough to carry the entire secret can permit exact recovery with probability one.” The neighboring theorem is a full-secret-capacity example, not a claim about every field described as free text.

**Claim 7, Does NOT say (b).** Replace it with: “The bound is for any fixed number m of items, including m=1. It does not cover unbounded or observation-dependent sequence lengths without modeling those observations.” Replace the bit-capacity gloss in (c) with: “The formal conclusion concerns exact recovery. For Kc ≥ 1, the number of possible fixed-length visible sequences is Kc^m, whose log2 cardinality is m log2 Kc.”

**Claim 10, missing normalization and traffic-law interpretation.** Replace the traffic-law premise with: “There is a schedule-independent certificate sigma on traffic decisions at each visible history g, with non-negative entries and sum_a sigma(g,a)=1. For every size-B audit schedule and every full history, the non-caught marginal for action a is bounded by sigma(g,a) times 1-r when that action sends traffic in an audited window, and by sigma(g,a) otherwise.” The original requires equality to one, not merely an upper bound. Its `hrec` constrains the non-caught marginal; it does not separately assert that sigma equals the complete action marginal of K, including caught branches.

No replacement is needed for the formal conclusion of claims 1, 8, or 9.

## Ambiguities exposed

The verdicts measure the frozen back translations against the original Lean declarations. They do not certify every sentence of surrounding English. In particular, claims 2, 4, 5, and 7 can have an EQUIVALENT back statement while retaining prose defects listed above.

The original declarations of claims 2 and 3 additionally quantify decidable-equality instances for their finite observation alphabets. Classical instances eliminate this typing difference in the gated schema proofs. It adds no security or probability premise. All back files compiled without repairs.

The “Does NOT say” boundaries were checked claim by claim:

| Claim | Hostile reading of the exclusions |
|---|---|
| 1 | (a)–(c) respected: no deployment observation closure, one-lineage restriction, empirical completion result, VM usefulness, or composition of the five separate facts is derived. The explicit warning that W need not be a probability kernel is accurate. |
| 2 | (a)–(c) respected: one final gateway view, no Python refinement proof, and an exact-recovery counting bound. The before/after-close defect is in the positive description. |
| 3 | (a)–(c) respected: no real lifetime/side-channel completeness or small ledger cap is established; the encoder is a joint tuple law. The independence wording needs the correction above. |
| 4 | (a)–(c) respected: certificates are premises, the payoff is exact recovery only, and extra observation channels are excluded. The word probability needs normalization. Domination is over every full hidden history, not just an average history. |
| 5 | (b)–(c) respected. (a) correctly makes deployment re-keying conditional, but the claim that any secret-carrying cache necessarily violates the premise is too broad. The statement imposes certificate domination, not an explicit hidden-state independence predicate. |
| 6 | (b)–(c) respected: fixed m rounds, lost mass not a visible absence symbol, no timing/error channels. (a) has the free-text overgeneralization corrected above. |
| 7 | (a) respected. (b) incorrectly excludes m=1. (c) is a counting interpretation for Kc ≥ 1, not a separate Lean theorem about meaning or information measures; Kc=0 is allowed by the formal statement. |
| 8 | (a)–(c) respected: abstract counts and a quota hypothesis; no clock, enforcement, or incompressibility result. |
| 9 | (a)–(c) respected: the event is success of the whole capped plan with no catch, with its product survival model. It does not silently replace this by prefix completion, prove the truncation bridge, or address a hidden fixed budget or additional channels. |
| 10 | (a)–(c) respected: exactly N windows, at least ceilDiv S q traffic windows and no catch; no quota/byte bridge, deployment schedule secrecy, or deployment recall proof. There is no positive-q hypothesis in this theorem. The certificate normalization is missing from the English. |

Non-vacuity witnesses use positive round counts, finite nonempty alphabets and secret spaces with multiple secrets where applicable. The SC-01 witness also realizes five ledger admissions. The SC-07 witnesses use positive quota and nontrivial recall/survival values. Claim 10 witnesses both the extra sub-distribution domain and a normalized original domain.

## Reproduction and integrity

Run from the repository root:

```bash
python3 docs/lean-english/one-to-one/blind-g1n2/regate.py
```

`regate.py` rechecks every saved statement and separately gates every claim and witness through the deterministic gate; any failure makes its exit status nonzero. It does not regenerate or rewrite statement/proof sources. Its persistent outputs are the JSON receipts and their text transcripts; the gate creates and removes temporary Lean check files.

`leangate_imports.py` is a byte-for-byte copy of the permitted helper: banned-token patterns, nonce assembly, output checks, and allowed axioms are unchanged. `run_gate_blind.diff` records the runner relocation and new imports/glob. The relocated runner requires `parents[4]` rather than `parents[3]` to resolve the repository root because this output directory is one level deeper. No gate security check was changed.

`typed/HASHES.json` was written at 2026-10-13T05:13:16.436475+00:00 before opening any original declaration. Every typed file is byte-for-byte identical to its verified Phase A back file. Per-claim compile logs and no-repair records are in `compile-logs/` and `compile-fixes/`. `COMPARISON-HASHES.json` freezes the saved comparison and witness sources; `SOURCE-HASHES.json` records the original source files read.

Only the allowed English input, claim list, back files/hash manifest, and gate helpers were read under `docs/lean-english/`. No earlier comparison results were used. No git command, download, ControlStack edit, or write outside this output directory was performed.
