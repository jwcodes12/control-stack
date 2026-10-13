from pathlib import Path
import hashlib,json
from datetime import datetime,timezone
OUT=Path(__file__).resolve().parent
notes={
1:'Identity lambda versus `id` reduces definitionally. Both outcome fields match. True-issuer caveat respected.',
2:'Same abstract `Good`, digest mode, roles, hash, and arbitrary operations. No review-target, runtime, or tag-mode guarantee added.',
3:'List membership and the original contents-in-play set give identical injectivity hypotheses; content equality is reversed symmetrically. No non-agent or competence claim added.',
4:'Same `Good` on the reached state: recorded applies and proposal-id uniqueness. No ceiling guarantee between applies or chronological approval predicate added.',
5:'Same one-step equality under `halted = false`. No scheduling, elapsed-time, or halted-state guarantee added.',
6:'Same equality of `applied` logs under `halted = true`. Non-vacuity witness retains an existing apply while an out-of-band operation changes `live`.',
7:'Explicit `decide` and the original predicate-to-Bool coercion reduce identically. Duplicate list entries count; no severity or ceiling guarantee added.',
8:'Same ghost-record membership and truncated natural-number clock subtraction. No direct live-list or real-time guarantee added.',
9:'Issuer-operation existentials equal direct trace membership; set/list adversary encodings agree under role disjointness. No authenticity for unclaimed operations, competence, or issuer-source guarantee added.',
10:'Same unauthenticated `live` and authenticated `applied` outcomes. Different observed fields and true-issuer caveat preserved.'}
receipts={}
for n in range(1,11):
 p=OUT/f'bg3n2_{n}.receipt.json'
 r=json.loads(p.read_text())
 assert r['passed'] and r['claim_passed'] and r['witness_passed'], n
 for kind in ('statement','proof'):
  assert r[f'{kind}_sha256']==hashlib.sha256((OUT/f'bg3n2_{n}.{kind}.lean').read_bytes()).hexdigest(), (n,kind)
 receipts[n]=r
clean=json.loads((OUT/'regate-clean-state.json').read_text())
assert clean['exit_code']==0 and clean['nonreceipt_files_unchanged']
rows=['| Claim | Verdict | Receipts | Note |','|---|---|---|---|']
for n in range(1,11):
 rows.append(f'| {n} | EQUIVALENT | [claim + witness PASS](bg3n2_{n}.receipt.json) | {notes[n]} |')
text='''# Blind g3n2: Phase B results

All ten frozen back-translations compiled as written. Every comparison and every non-vacuity witness passed the deterministic gate independently: 10 claim passes and 10 witness passes. No English/formal mismatch was found in the reconstructed theorem propositions. The suggested English replacements below resolve ambiguities; they do not change a certified verdict.

'''+ '\n'.join(rows)+'''

## How the comparisons were made

All Phase A hashes were checked against `back/BACK-HASHES.json`. Compilation logs are in `compile-logs/`; `compile-fixes/1.diff` through `10.diff` each report that no repair was required. Each `typed/` file is byte-identical to its back file. `typed/HASHES.json` was saved at 2026-10-13T04:30:02.658865+00:00, before any original declaration was opened. Only then were the original declarations located in `ControlStack/`. `ORIGINAL-SOURCES.json` records the relevant source-module hashes. No git command was run, no download was performed, and no project source was edited.

Each saved statement copies the exact frozen back proposition into `BackClosed`, preserving its expression while changing only its local definition name and namespace. For the quantified claims, a gated `Iff.rfl` links that expression to the parameterized `BackAt` comparison. `OrigAt` transcribes the original conclusion. `OrigClosed` preserves the original hypothesis and binder ordering; `OriginalDeclaration : OrigClosed := @<original theorem>` makes the deterministic statement check verify the transcription against the actual imported declaration. This type-checking definition is not used to prove the iff. The comparison proofs never invoke an original safety theorem to infer a conclusion, and never derive equivalence merely because both closed statements are true.

For claims 1 and 10 the fixed negative-control propositions themselves are definitionally identical, so their comparisons use `Iff.rfl`, independently of their computational truth. For claims 2, 4, 5, 6, 7 and 8, the gate proves an iff between conclusions for the same parameters, using the same hypotheses where present. Claims 3 and 9 also establish the following explicit bridges:

- **Claim 3:** For any abstract state, membership in the concatenated deployed/reviewed content maps is equivalent to membership in the original contents-in-play set. The two injectivity hypotheses are therefore equivalent. For any roles and state, the two reviewed-content conclusions are equivalent by symmetry of content equality. These proofs do not require reachability or assume either original conclusion.
- **Claim 9:** For an adversary list `UL`, the set `{c | c ∈ UL}` gives exactly the original disjointness hypothesis. The gate additionally compares the conclusions for any abstract state, input trace, adversary set `US`, and adversary list `UL`, whenever both exclude reviewers. In each direction it reconstructs/eliminates the original issuer-operation existentials and obtains non-adversary membership from reviewer membership and disjointness. It uses neither `sc17_safe_authenticated` nor `sc17_safe` for this iff. Taking `UL = []` transports the original conclusion to any adversary set under its disjointness premise; taking `US = {c | c ∈ UL}` gives the direct list representation. The representation change adds no observable conclusion under the common role-disjointness condition.

## Non-vacuity and gate evidence

The witnesses exercise these concrete, non-degenerate cases:

| Claim | Witness |
|---|---|
| 1 | The fixed forged trace really produces a deployment without authentication and an empty deployment log with it. |
| 2 | A concrete put/review/approve/deploy trace produces deployment `(0,5,7)` and satisfies `Good`. |
| 3 | The same trace has nonempty deployment and review logs, with identity-hash injectivity. |
| 4 | An honest reviewed proposal produces applied id `0` and satisfies `Good`. |
| 5 | A non-halted state starts with unequal live/desired lists; one reconcile makes them equal. |
| 6 | A halted state already has an apply record; subsequent out-of-band mutation changes live while the applied log stays equal. |
| 7 | Positive rate and period, nonempty desired list, and two identical out-of-band entries produce count two, within the bound. |
| 8 | A recorded out-of-band entry is one tick old under a positive period of three ticks. |
| 9 | Adversary issuer `1` is disjoint from reviewer `2`; the authenticated trace has an approval from issuer `2`, a proposal from issuer `1`, and a nonempty applied log. |
| 10 | The fixed forged trace produces the specified live grant without authentication and an empty applied log with it. |

`leangate_imports.py` is byte-identical to the allowed gate helper; no banned-token or axiom check was changed. `run_gate_blind.py` changes the import list, claim glob, and root-depth path adjustment required by moving the runner into this output directory. The common import header is `ControlStack.Scenarios.AuthInstancesA ControlStack.Scenarios.SC16Refinement ControlStack.Scenarios.SC17Drift`. The project path is this repository root. `GATE-PROVENANCE.md` describes these changes.

Each `bg3n2_<n>.receipt.json` contains separate statement, claim, and witness results, nonce-bearing axiom reports, hashes, imports, and project path. Final proofs use only allowed standard axioms; none uses `sorryAx`. The initial failed comparison-proof attempts are retained in `initial-gate-failures/` for audit. They were namespace/unfolding errors in Phase B proof scaffolding, not repairs to Phase A statements.

`regate.py` loads the same runner and deterministic gate, checks all ten expected ids (missing files fail), gates both theorem targets separately, rewrites only receipts, and exits nonzero on any failure. Its first run did exit nonzero on proof errors. The final clean-state run started with no receipts or gate scratch directory, returned zero, and verified that all other saved file bytes stayed unchanged; see `regate-clean-state.json`. Temporary Lean check files are removed by the unchanged gate. From the repository root, rerun with:

```sh
python3 docs/lean-english/one-to-one/blind-g3n2/regate.py
```

## Corrections to the English

No correction to a theorem's mathematical content is required by these verdicts. These replacement sentences remove wording that could invite a stronger or different reading:

1. **Claim 2, nonce scope:** Replace the end of the main sentence with: “Every deployment has a matching approval nonce and target, its content hashes to the approved digest, that digest has a review by a listed reviewer distinct from the recorded stager, and the deployment log's nonce values have no repeats.” `Good` concerns deployment nonces, not a blanket uniqueness property of every nonce-bearing field.
2. **Claim 4, list semantics and record scope:** “For arbitrary initial grant lists and an arbitrary ceiling predicate on grant lists, every apply record produced with all four checks enabled records equal live and desired lists, passes the ceiling predicate, and has a final-log approval with the same proposal id and diff from a listed reviewer distinct from the record's author; applied proposal ids have no repeats.”
3. **Claim 5, equality semantics:** “From any state with `halted = false`, one reconcile with the deployed checks makes the model's live grant list exactly equal to its desired grant list.”
4. **Claim 7, unit being counted:** “For every operation list, with `0 < W`, scheduler enabled, and at most `d` accepted out-of-band additions in each model tick, the final live list contains at most `d * W` entries whose grant value is absent from the desired list; repeated entries count separately.” Arbitrary operation lists include every trace prefix.
5. **Claim 8, ghost-record scope:** “In the scheduled drift model with `0 < W`, every `(grant, birthTick)` entry in the final ghost drift list satisfies `clock - birthTick < W`; the separate `live_eq` theorem connects those entries to the added live-list occurrences.”
6. **Claim 9, concrete representation:** “For any finite list `U` of adversary issuer ids disjoint from the reviewer list, every final approval has an input operation issued by its recorded reviewer, and every final proposal version has an input propose/amend operation issued by its recorded author.” The original uses a list; the back uses a set, whose membership interpretation was explicitly bridged above. Neither formulation adds a cryptographic issuer-source theorem.

## Ambiguities exposed

- **“Grant set” versus grant list (claims 4–5 and the SC-17 descriptions):** `G` is a triple, but states store lists of triples. Equality preserves order and multiplicity, and the arbitrary `allowed : List G → Bool` may inspect either. A mathematical set interpretation is therefore ambiguous. Claim 7 explicitly preserves duplicate counting, as its English caveat says.
- **“First stager kept” (claims 2–3):** The concrete store retains the first accepted `(content, stager)` pair for a digest, not merely its stager identity. With collisions, a later content having that digest is ignored. The restricted injectivity hypothesis in claim 3 was preserved and its two encodings proved equivalent; this audit does not establish the suggested separate theorem that the hypothesis can be removed.
- **Reviewer versus non-agent (claim 3):** The formal conclusion requires reviewer-list membership and inequality with the review row's recorded stager. It contains no reviewer/agent disjointness assumption. The “Does NOT say” warning is respected.
- **Current live state versus historical record (claim 4):** `Good` tests the live list stored in each apply record, not the reached state's live list after later out-of-band changes. The no-between-applies ceiling warning is respected. Final-log approval existence has no explicit timestamp/order predicate; that absence should not be read as a counterexample to the operational requirement for a pre-existing approval.
- **Halt scope (claims 5–6):** The equality is about `applied`, and a halted state still accepts out-of-band live mutations. The claim-6 witness certifies this distinction. The arbitrary halted-state hypothesis does not require proving that its flag originated from an authorized halt operation.
- **Clock, rate, and ghost state (claims 7–8):** Ticks are trace operations, excess additions are ignored by the model's rate counter, and the lifetime is stated on the ghost drift record. The warnings about severity, ceiling, scheduler absence, real time, and the separate model are all respected. The checks do not establish real reconciler success or a connection to SC-17 proposals/applies.
- **Adversary “set” (claim 9):** The back's arbitrary set and original's finite list differ as types. Role-disjointness makes the non-adversary approval conjunct follow from reviewer membership, allowing the gated pointwise transport for both representations. Duplicates in the original list have no effect on membership. The English does not assert an infinite-adversary extension explicitly, so the proposed sentence states the original list representation.
- **Different observed fields (claim 10):** The unauthenticated side tests `live`, while the authenticated side tests `applied`. Both the original and the back preserve this, and the English expressly warns about it.
- **Trusted identities and runtime (claims 1–6, 9–10):** Imported model operations believe caller identities; the authenticated instances filter claims against provided issuer numbers. No comparison or witness proves that a platform supplies true issuers, that signing keys are secure, that reviewers are competent, or that Python/cluster behavior implements these machines. The corresponding “Does NOT say” caveats remain intact.
'''
(OUT/'RESULTS.md').write_text(text)
now=datetime.now(timezone.utc)
start=datetime.fromisoformat('2026-10-13T04:29:00+00:00')
progress=f'''# Phase B progress

Done: all 10 claims compiled unchanged, typed hashes frozen before opening original declarations, 10 pointwise comparisons gated, 10 non-degenerate witnesses separately gated, hostile English audit completed, and RESULTS.md written. Final clean-state regate passed all 20 theorem targets and changed only receipts. No claim is unfinished or UNDECIDED.

Not done: no required work remains. Real-platform identity authenticity, cryptography, runtime implementation, real-time reconciliation, and the possible removal of claim 3's injectivity hypothesis were not proved; they are outside these ten comparisons.

Time: began approximately 2026-10-13T04:29:00Z; typed freeze 2026-10-13T04:30:02.658865+00:00; completed {now.isoformat()} (approximately {(now-start).total_seconds()/60:.1f} minutes). Clean-state regate took {clean['seconds']:.1f} seconds.

What could not be done: nothing within the requested scope. Initial Phase B proof scaffolding failed on namespace/unfolding issues and was corrected; failed receipts remain archived. No repair to a back file was needed. No files outside blind-g3n2 were intentionally written; no ControlStack edit, git command, download, or forbidden English-results read was performed.
'''
(OUT/'PROGRESS.md').write_text(progress)
print('RESULTS.md and PROGRESS.md written after all final receipts passed.')
