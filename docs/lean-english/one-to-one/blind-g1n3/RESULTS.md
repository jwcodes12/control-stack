# Blind g1n3 — Phase B results

All nine back translations are **EQUIVALENT** to the original statements, pointwise under matching hypotheses. All nine comparison gates and all nine separate witness gates passed. These are statements about the specified models; they do not certify a deployed gateway or a probabilistic correspondence to real audits.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — `ControlStack.SC07Exfil.expected_leak_le` | EQUIVALENT | [claim](bg1n3_1.receipt.json), [witness](bg1n3_1.witness.receipt.json) | Identical conclusions and hypotheses; only binder order differs. |
| 2 — `ControlStack.SC07Exfil.observable_schedule_exfil` | EQUIVALENT | [claim](bg1n3_2.receipt.json), [witness](bg1n3_2.witness.receipt.json) | Capping `[0,q,0,q]` at q leaves the list unchanged. |
| 3 — `ControlStack.SC07Exfil.datacenter_example` | EQUIVALENT | [claim](bg1n3_3.receipt.json), [witness](bg1n3_3.witness.receipt.json) | Exact fraction/decimal agreement; the independent ceiling fact can move outside the plan hypotheses. |
| 4 — `ControlStack.SC07Liveness.upload_completes` | EQUIVALENT | [claim](bg1n3_4.receipt.json), [witness](bg1n3_4.witness.receipt.json) | Same arbitrary starting state and ordered log extension. |
| 5 — `ControlStack.SC07Liveness.exfil_needs_windows` | EQUIVALENT | [claim](bg1n3_5.receipt.json), [witness](bg1n3_5.witness.receipt.json) | Same bound on windows opened, including the initial window. |
| 6 — `ControlStack.SC07Liveness.shared_quota_blocks` | EQUIVALENT | [claim](bg1n3_6.receipt.json), [witness](bg1n3_6.witness.receipt.json) | The two concrete log equalities are definitionally identical. |
| 7 — `ControlStack.SC07Refinement.concrete_wire_lt` | EQUIVALENT | [claim](bg1n3_7.receipt.json), [witness](bg1n3_7.witness.receipt.json) | Same initial state, quota-rule premise, positive Q, and strict wire bound. |
| 8 — `ControlStack.SC07Refinement.concrete_halt_freezes` | EQUIVALENT | [claim](bg1n3_8.receipt.json), [witness](bg1n3_8.witness.receipt.json) | Same prefix/continuation statement; the forwarded list freezes. |
| 9 — `ControlStack.SC07Refinement.sink_within_quota` | EQUIVALENT | [claim](bg1n3_9.receipt.json), [witness](bg1n3_9.witness.receipt.json) | Same conditional pair of bounds, including natural-number subtraction when Q = 0. |

## Evidence and comparison method

Every raw back file was submitted to `lake env lean` unchanged. Each needed its project import; claim 8 additionally required escaping the reserved binder `prefix` as `«prefix»`. These repairs change no meaning. The nine diffs are in [compile-fixes](compile-fixes/), the compiler output in [compile-logs](compile-logs/), and the successful repaired files in [typed](typed/). All back SHA-256 values matched `back/BACK-HASHES.json`. [typed/HASHES.json](typed/HASHES.json) was written after all nine repaired files compiled and before any original declaration was opened.

The original declaration headers, source locations, and source hashes are saved in [originals](originals/). The comparison statements and proofs are `bg1n3_<n>.statement.lean` and `bg1n3_<n>.proof.lean`. Each statement embeds the frozen repaired back body as `FrozenBack`, factors out its pointwise conclusion as `BackAt`, and spells out the original conclusion as `OriginalAt`. Each `Claim` proves both the faithful reconstruction of the back statement and `BackAt ↔ OriginalAt` under the same hypotheses. The supporting `original_signature` in each proof file type-checks `OriginalAt` against the named original theorem.

For claims 1, 4–9, the pointwise iff is proved by reflexivity. Claim 6 has no variable inputs: its concrete conjunction is definitionally the same on both sides, and the proof is reflexivity rather than an inference from two closed true theorems. Claim 2 simplifies the capped list. Claim 3 normalizes exact real literals, and its reconstruction proves the independent ceiling equality arithmetically before placing it outside the quantifier. None of these comparison iffs is obtained merely by invoking the truth of both original and back theorems.

The gate embedding changes the back declaration's name and replaces its enclosing namespace with an `open` inside the required `PL_bg1n3_<n>` namespace. Claim 8's bound variable names become `pre` and `post` in that embedding: even escaped `prefix` would match the gate's unchanged raw-token ban. This is alpha-renaming only; the hashed typed file remains untouched. [build_comparisons.py](build_comparisons.py) checks the frozen typed hashes before producing the comparison files.

[run_gate_blind.py](run_gate_blind.py) is the supplied runner with only its output-directory assignment, statement glob, and `PL_IMPORTS` changed; [gate-runner.diff](gate-runner.diff) records these edits. The output-directory assignment also restores the repository ROOT after moving the script one directory deeper. The copied [leangate_imports.py](leangate_imports.py) is byte-for-byte identical to the permitted helper. Its banned-token checks, nonce checks, and allowed-axiom set remain unchanged. All observed axiom reports are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g1n3/regate.py
```

[regate.py](regate.py) checks all nine statements and gates `claim` and `witness` separately for each. It preserves the saved statement/proof files, rewrites only receipts as persistent outputs, and exits nonzero if any check fails or an expected file is absent. [REGATE-VALIDATION.json](REGATE-VALIDATION.json) records a successful clean run after deleting receipts, temporary gate files, and Python caches: 18 passing receipts, exit code 0, and no persistent nonreceipt changes. [SAVED-HASHES.json](SAVED-HASHES.json) records the final statement, proof, and helper hashes. Receipts contain the statement/proof/helper hashes and the gate output.

## Hostile reading, claim by claim

1. **Expected leakage.** The hypotheses and conclusion agree exactly. The witness has q = 8, pr = 1/2, two full windows, and expected leakage 12 bits. “Does NOT say” (a)–(c) are respected: the conclusion is an expected value, real audit independence and stopping behavior are modelling assumptions, and the recursion counts the catching window's bits. Zero-count windows have survival multiplier 1, so timing or zero-size covert encodings are outside this bit-count model. Calling every `c i` an actual unconditional catch probability is ambiguous when the window carries zero bits; see the replacement below.

2. **Observable schedule.** The back's uncapped plan is the original's capped plan because all four entries already lie between 0 and q. The witness uses q = 1 and checks two bits with survival 1. “Does NOT say” (a)–(b) are respected. This is an evasion example in a schedule with zero catch probability on traffic windows; it does not refute the bound under a positive uniform catch lower bound. Known scheduling is illustrated by one selected plan, rather than a formal attacker-information structure.

3. **Datacenter example.** `5/100 = 0.05` and `6/1000 = 0.006` are exact real equalities. The ceiling fact is constant and is proved independently when reconstructing the back's outer conjunction. The witness has 100 full quota windows and catch parameter 1 at every index, satisfying the actual large-target premise. “Does NOT say” (a)–(b) are respected: there is no empirical recall claim or lower bound on information needed to reconstruct an artifact. Item (c) points outside the supplied English to a caveat rather than stating it. The formal conclusion uses survival of the entire capped plan, including any traffic after its first attainment of S; that caveat should be written directly.

4. **Upload completion.** The back and original quantify over every starting state, including unreachable states, and have exactly the same halted, allowlist, and remaining-quota premises. The witness forwards chunks 5 and 3 in window 0. “Does NOT say” (a)–(c) are respected: the operation list contains only the upload's sends, there is no runtime byte-exactness result, and an oversized upload is outside the hypotheses.

5. **Windows needed.** The formula is identical after reordering binders. The witness forwards 16 bits through q = 8 using two windows. “Does NOT say” (a)–(b) are respected: arbitrary traces may tick freely, and the result says nothing about catching. A further distinction matters for the advertised bridge: the right side counts windows opened, including empty windows; it is not the `traffic` count in `SC07Exfil.windows_needed`. This theorem alone supplies neither a traffic-bearing-window count nor an independently audited time model.

6. **Shared quota.** Both fixed log equalities are identical after constructor elaboration. The witness also checks allowlist `[10]` and quota 8. “Does NOT say” (a)–(c) are respected. The model has no job identifier: “another job” and “honest” describe the interpretation of the two sends, not additional state or proven isolation properties.

7. **Strict wire bound.** The original has exactly the reconstructed formal premises `quotaRule = true` and `0 < Q`, with runs starting at `cinit`; there are no additional correspondence hypotheses in its type. The witness forwards 5 wire bytes in each of two windows with Q = 10. “Does NOT say” (a)–(b) are respected: the bound is per window, reset operations are permitted, and the kernel's behavior is not proved. The back author's recorded uncertainty about unspecified correspondence assumptions therefore hides no missing formal premise, but the English should identify its model explicitly.

8. **HALT.** The binder repair and gate alpha-renaming preserve the formula. The witness has a nonempty forwarded prefix, then HALT, then a quota reset and another packet; its forwarded list remains unchanged. “Does NOT say” (a)–(b) are respected. Only the forwarded list freezes: for example, reset and dropped-packet bookkeeping can still change other fields after HALT.

9. **Sink bound.** The premises and both conclusions agree exactly. The witness instantiates the assumed sink count at a positive 4 under Q = 10 and tolerance 1500. “Does NOT say” (a)–(c) are respected: the selected window is essential, delivery is not guaranteed, and the bound follows from `concrete_safe` plus `hsink`. No positivity assumption on Q is missing: natural subtraction saturates at zero, and the formula remains meaningful at Q = 0. The wording “not provable in Lean” is too broad; the gateway model alone does not establish the physical sink correspondence. A separate delivery model could formalize and prove such a relation.

## Corrections to the English

No mathematical conclusion requires correction. The following replacement sentences remove ambiguous interpretations without changing the matched claims.

- **Claim 1, catch probabilities:** “For every index i, choose a catch parameter c i between pr and 1, with pr > 0. The recursion applies that parameter only when the quota-capped window carries positive traffic; zero-count windows contribute no catch factor.”
- **Claim 2, interpretation of the negative control:** “This fixed plan evades the chosen observable schedule because its traffic windows have catch probability zero; the positive uniform catch-lower-bound premise of the exfiltration bound is unavailable.”
- **Claim 3, replace the external caveat reference:** “This bounds survival through every traffic-bearing window of the entire capped plan. If the plan continues after first reaching S, this is a whole-plan survival statement, rather than a direct statement about survival only until first completion.”
- **Claim 5, bridge interpretation:** “At least ceil(S/q) windows have been opened, counting the initial window and allowing empty windows. Ticks may occur freely in the trace; this count alone establishes no elapsed-time bound, traffic-window count, or audit-probability bound.”
- **Claim 7, model assumptions:** “In the concrete `runC` model starting at `cinit`, with natural payload and header lengths, `quotaRule = true` and Q > 0 suffice for the strict per-window wire bound. Relating this model to a deployed gateway requires separate correspondence assumptions.”
- **Claim 9, sink premise:** “Assume the measured sink count is at most the forwarded payload bytes attributed to the chosen window w. This correspondence is an input premise; the gateway model does not establish TCP delivery or measurement behavior. Under that premise the count is at most Q − 1, and at most Q plus any natural tolerance.”

## Ambiguities exposed

- **Catch parameter versus actual catch event:** a positive `c i` coexists with a zero-bit window that is never caught because the recursion skips the catch factor for that window. Independence is part of the probabilistic interpretation of the recursion, not a theorem about real events.
- **Whole-plan survival versus first completion:** a bound on the former is not, by itself, a bound on the latter for a longer plan. Claim 3's current cross-reference leaves this distinction unstated in the supplied English.
- **Opened windows versus traffic-bearing windows:** claim 5 counts ticks plus one; the exfiltration model counts positive traffic entries. A claimed bridge between those counts needs additional modelling work.
- **Unspecified correspondence assumptions:** claim 7's formal theorem has just the two stated configuration premises. Deployment assumptions should be kept explicit in the prose instead of being hidden behind another theorem's name.
- **Sink scope and formalizability:** no-duplicate delivery alone does not align a whole-run sink count with one chosen window. `hsink` must refer to compatible counters and windows. It is assumed here, rather than inherently beyond formal proof.
- **Job labels and frozen state:** claim 6's jobs are explanatory labels; claim 8 freezes forwarding only. Neither theorem establishes a richer concurrency or complete-state guarantee.
