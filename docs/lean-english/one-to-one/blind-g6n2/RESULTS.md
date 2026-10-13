# Blind g6n2 Phase B results

Eight claims have certified pointwise equivalence. Claims 4 and 8 are **UNDECIDED** for the requested same-run equivalence: their original-to-back implications and conclusion-shape diagnostics passed, but no reverse implication for the stated runs was certified. Their diagnostic counterexamples are explicitly not counterexamples to the deployed machines.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1 — `safe_of_sound` | EQUIVALENT | [claim](bg6n2_1.receipt.json), [witness](bg6n2_1.witness.receipt.json) | Identical `Good` conclusion for every symbolic state; five `Sound` flags, legal trace, initial state match. |
| 2 — `sc26_safe_disjoint` | EQUIVALENT | [claim](bg6n2_2.receipt.json), [witness](bg6n2_2.witness.receipt.json) | Identical per-entry request, exact approval, role exclusion and requester inequality. |
| 3 — `sc26_once` | EQUIVALENT | [claim](bg6n2_3.receipt.json), [witness](bg6n2_3.witness.receipt.json) | Identical reservation-list `Nodup`; no legality premise was introduced. |
| 4 — `halt_freezes` | UNDECIDED | [direction/diagnostics](bg6n2_4.receipt.json), [witness](bg6n2_4.witness.receipt.json) | Original list equality implies Back set equality. Converse conclusion predicates differ; no same-run converse certificate. |
| 5 — `concrete_safe` | EQUIVALENT | [claim](bg6n2_5.receipt.json), [witness](bg6n2_5.witness.receipt.json) | Identical `Good` of abstraction `α`; legal concrete trace and fixed recovery flag `true` match. |
| 6 — `concrete_halt` | EQUIVALENT | [claim](bg6n2_6.receipt.json), [witness](bg6n2_6.witness.receipt.json) | Identical wire list equality and initial-bank/initial-wire membership bound. |
| 7 — `sc26_safe_authenticated` | EQUIVALENT | [claim](bg6n2_7.receipt.json), [witness](bg6n2_7.witness.receipt.json) | Identical `Good` and self-issued approval provenance; both hypothesis rewritings certified. |
| 8 — `forged_approval_pays_without_auth` | UNDECIDED | [direction/diagnostics](bg6n2_8.receipt.json), [witness](bg6n2_8.witness.receipt.json) | Original singleton equality vs Back membership; original excludes one exact approval, Back excludes every approver-issued operation. Fixed-trace converse not certified. |
| 9 — `sc26_consent_from_honest_script` | EQUIVALENT | [claim](bg6n2_9.receipt.json), [witness](bg6n2_9.witness.receipt.json) | Identical honest-script approval provenance and `AdvTrace`; hypothesis rewritings certified. |
| 10 — `honest_progress` | EQUIVALENT | [claim](bg6n2_10.receipt.json), [witness](bg6n2_10.witness.receipt.json) | Identical membership after consecutive execute/deliver/arrive; all six state premises retained. |

## Method and certification boundary

Only the authorized input batch, `CLAIMS.txt`, back files/manifest and three gate helpers were read under `docs/lean-english/`. No previous comparison was read. No git command was run; no download or source edit was performed. Every write was inside this result directory.

All ten back files were compiled **as written** first; each failed for missing imports. Each typed repair adds exactly one project-module import and a blank line. No proposition body was edited. The repairs and their no-meaning-change explanations are in [compile-fixes](compile-fixes/); initial and repaired compiler output is in [compile-logs](compile-logs/). Every Phase A hash matched `back/BACK-HASHES.json`. All repaired files compiled, and [typed/HASHES.json](typed/HASHES.json) was written before the first original source was opened. That manifest records this boundary. [ORIGINAL-SOURCE-HASHES.json](ORIGINAL-SOURCE-HASHES.json) identifies the five original modules subsequently examined.

Each saved statement contains `Back`, transcribed from the frozen typed proposition body, plus `BackEnvelope`, `BackAt`, `OrigEnvelope`, and `OrigAt`. Each certificate proves `Back ↔ BackEnvelope`. Each proof file also typechecks `original_signature : OrigEnvelope` against the named original declaration, with its actual binder order. For the eight EQUIVALENT verdicts, the comparison is `BackAt ↔ OrigAt` on arbitrary symbolic observations, by definitional identity. These proofs do not use `original_signature` or the original safety/progress theorem as a reason that both sides are true. Claims 7 and 9 separately prove equivalence of the differently oriented disjointness hypotheses and of the pattern-match vs quantified bank-call hypotheses. Consequently the hypotheses also agree.

For claim 4, the certificate proves `OrigEnvelope → Back`, and, more strongly, `OrigAt s t → BackAt s t` for arbitrary observations. A halted symbolic `s` with `net = [(0, tx1)]` and symbolic `t` with `net = [(0, tx1), (0, tx1)]`, both with empty banks, satisfy the Back conclusion and fail the original conclusion. This diagnoses loss of list multiplicity in the English/back formulation. **It does not assert `t = run R cap full s ops` for any legal continuation.** Thus it does not certify DIFFERENT or a strict ENGLISH_WEAKER verdict under the actual run hypotheses. A reverse proof obtained solely by invoking `halt_freezes` would disregard the requested protection against manufacturing equivalence from two true propositions; none is supplied.

For claim 8, a structural induction proves that authentication with a constantly absent claim is the raw run on issuer-erased operations. The certificate uses this to prove `OrigEnvelope → Back`. It also compares the conclusion predicates on explicit symbolic observations: a duplicated bank list with the fixed `forged` script satisfies Back and fails Orig; an otherwise singleton/empty-bank observation with script `[(2, deliver 0)]` satisfies Orig's lack of the particular self-issued approval but fails Back's absence of all approver-issued operations. **Neither diagnostic substitutes a different actual run or trace into the fixed-trace theorem.** On the actual five-element `forged` trace, both assertions hold, as the evaluated facts in the proof/witness show. Turning that fact alone into an iff would be precisely the closed-true-theorem shortcut the instructions prohibit. The requested equivalence therefore remains uncertified.

Every `Witness` is substantive: claims 1–3 and 5 use a legal positive-amount payment; claims 4 and 6 start halted with an unpaid in-flight message and show it landing; claim 7 uses a genuine authenticated approver; claim 8 exercises the five-operation forgery; claim 9 uses a nonempty honest approval and a genuine order-preserving adversary interleaving; claim 10 supplies an approved, unreserved, invariant-satisfying request with cap headroom and shows payment.

[run_gate_blind.py](run_gate_blind.py) is the supplied runner relocated here. Its only configuration changes are the root path correction required by the extra directory level, the statement glob, and `PL_IMPORTS`; [run-gate-config.diff](run-gate-config.diff) records them. The gate helper [leangate_imports.py](leangate_imports.py) is byte-identical to the authorized helper. No banned-token or axiom check was changed. Claim and Witness have separate nonce-bearing axiom reports and separate receipts. Initial failed proof attempts are retained in [gate-attempts](gate-attempts/); their failures were ordinary namespace/decidability issues in Phase B proofs, not edits to the frozen back statements.

[regate.py](regate.py) rechecks all ten saved statements, gates `claim` and `witness` separately, rewrites only their JSON receipts, and exits nonzero on any failure or missing/extra statement. It uses the exact imports/project/scratch paths of `run_gate_blind.py`, creates fresh temporary Lean check files through the unchanged gate, and needs no existing receipt or scratch directory. Run from the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g6n2/regate.py
```

[PROOF-HASHES.json](PROOF-HASHES.json) freezes the final twenty statement/proof files. The clean-state re-gate removed current receipts and the empty scratch directory before regenerating receipts from those files. Its result is recorded in [PROGRESS.md](PROGRESS.md).

## Corrections to the English

These are proposed replacements only; the input batch and part files were not edited.

**Claim 4 — replace the main sentence:** “For any starting state `s` with `s.halted = true`, after any legal continuation under the deployed checks, the entire ordered message list `net` is exactly equal to `s.net`, including multiplicities. Every final bank entry belongs to `s.bank` or `s.net`. Previously transmitted messages may still be recorded in the bank.” This matches the original list equality rather than only its set-valued consequence. Remove the suggestion that an authentic admin halt is a formal hypothesis of this theorem: the theorem assumes the flag, without requiring a history that explains it.

**Claim 8 — replace the main sentence:** “For the specified five-operation trace, the run with identity checking disabled has bank list exactly `[(0, tx1)]`; the trace contains no `approve a 0 tx1` issued by that same `a` for any `a` in the approvers list; and the identity-checked run has an empty bank.” Add separately, if desired: “In this particular trace every issuer is agent 1, so no approver issues any operation.” The latter is an additional true fact about the trace, stronger than the provenance conjunct in the original declaration. Membership alone omits the original's exact singleton-bank conclusion.

**Claim 6 — tighten the unsent-intent qualification:** “After halt, no new entry absent from both the initial bank and the initial wire can appear in the bank. Recovery and transmit cannot add to the wire.” This avoids suggesting that an arbitrary starting state's logged-intent row proves the corresponding entry was not already paid or transmitted through another row.

**Claim 10 — make the main sentence carry its listed premise:** “In an invariant-satisfying, non-halted state, take an unreserved request with an exact approval from a non-requester approver and enough remaining cap. Consecutive execute, deliver and arrive steps put its request payload in the bank.” Keep the existing note that the original proof does not use unreservedness; deleting that premise would formulate a separate stronger theorem rather than transcribe this declaration.

## Ambiguities exposed

1. **Collection precision (claims 4 and 8).** “Set unchanged” erases list order and multiplicity. “Bank holds the entry” expresses membership, not an exact singleton list. Both are safe consequences of the originals but insufficient for a structural one-to-one transcription.
2. **Scope of the negation in claim 8.** “No approver issued anything” quantifies over every operation. The original quantifies over one exact self-issued approval of key 0 and `tx1`. These agree on the chosen script but have different general conclusion predicates.
3. **Assumed flag vs authenticated history (claim 4).** An arbitrary halted starting state need not be reachable or have been halted by an actual admin. The discussion of admin authenticity is correspondence context, not an extra theorem premise.
4. **Single reservation vs other forms of one-use (claim 3).** The literal conclusion is only `reserved.Nodup`. “Charged at most once” describes the accompanying execute transition, which appends a reservation and increments spending together; the declaration does not separately quantify over charge events. Approvals persist, request ids distinguish equal business payloads, and receiver uniqueness belongs to the safety theorem.
5. **Concrete vs abstract in-flight meaning (claims 5 and 6).** The abstraction maps durable delivery-intent rows to abstract `net`, whereas concrete `wire` records physical transmissions. “Stronger than abstract halt” is meaningful through that abstraction/invariant context, not as an unqualified comparison of arbitrary unrelated states.
6. **Untrusted set vs constrained adversary (claims 7 and 9).** Claim 7 only assumes `U` is disjoint from approvers; the arbitrary trace need not be issued from `U`. Claim 9 adds `AdvTrace`, which really does confine the adversary script's issuers to `U`. The English preserves this distinction.
7. **Unused premise vs absent premise (claim 10).** The unused unreservedness hypothesis is still in both statements. No-interference, no timing guarantee, and membership rather than uniqueness are also preserved.

### “Does NOT say” audit

| Claim | Audit |
|---|---|
| 1 | Respected: only `Good` drops nonce/halt requirements; no general redundancy or halt guarantee is inferred. |
| 2 | Respected: exclusion is between identity lists, not humans or trustworthiness; role disjointness is assumed. |
| 3 | Respected: reservation uniqueness neither consumes approval records nor identifies equal business payloads nor guarantees bank delivery uniqueness. |
| 4 | Respected for post-halt arrivals, absence of promptness and absence of cancellation semantics. The formal assumption is the halted flag alone; set/list precision needs the correction above. The witness actually pays after halt. |
| 5 | Respected: machine safety does not establish Python correspondence, SQLite/OS premises or liveness. |
| 6 | Respected for messages already on the wire and absence of future transmissions. Tighten the unsent-intent sentence as above because arbitrary starting states can already have relevant bank/wire entries. The witness actually pays after halt. |
| 7 | Respected: no confinement to `U`, coercion guarantee, or extra requester guarantee is introduced. Hypothesis equivalences were proved, not assumed. |
| 8 | Respected: all assertions concern the one fixed trace, not general security of the guard. The positive and negative computations are witnessed. The exact strength of its two changed conjuncts needs clarification. |
| 9 | Respected: honest-script membership is the meaning of consent here; informed consent, freedom from manipulation, and further ordering guarantees are absent. |
| 10 | Respected: the three steps are consecutive; the conclusion is membership; promptness, existence of approval/headroom and resistance to interference are not asserted. |
