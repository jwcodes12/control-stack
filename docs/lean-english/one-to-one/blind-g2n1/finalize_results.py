"""Write the final report only after checking all current gate receipts."""
from pathlib import Path
import datetime, hashlib, json
OUT=Path(__file__).resolve().parent
names=['SC08.sc08_safe','SC08.safe_of_sound','SC08.halt_freezes','SC09.sc09_safe','SC09.spawn_attenuates','SC09.halt_freezes','SC10.sc10_safe','SC10.policy_admin_only','SC10.halt_freezes','SC12.sc12_safe']
notes=[
'Identical initial state and conclusion; expanded RunOk matches the English.',
'Back admits either initial halted flag; original fixes false. Strict scope extension, with matching conclusions on the original domain.',
'Whole-state equality under the same halted hypothesis.',
'Same two Good fields: granted lineage capabilities and grant-or-exact-rule uses.',
'List membership inclusion is exactly the original List subset relation; q/keep parameter order is aligned explicitly.',
'Whole-state equality under the same halted hypothesis.',
'Same hpin hypothesis, decision freshness/value/writer condition, and build digest condition.',
'Same hpin hypothesis retained, although irrelevant to writer membership.',
'Whole-state equality under the same halted hypothesis.',
'Same registration, active origin, and never-ended origin condition; bypass has no claimed label parameter.',
]
rows=[]
proof_hashes={}
for n,name in enumerate(names,1):
    cid=f'bg2n1_{n}'
    sp=OUT/f'{cid}.statement.lean'; pp=OUT/f'{cid}.proof.lean'
    sh=hashlib.sha256(sp.read_bytes()).hexdigest(); ph=hashlib.sha256(pp.read_bytes()).hexdigest()
    for suffix in ('receipt.json','witness.receipt.json'):
        r=json.loads((OUT/f'{cid}.{suffix}').read_text())
        assert r['passed'] and r['statement_passed'], (cid,suffix)
        assert r['statement_sha256']==sh and r['proof_sha256']==ph, (cid,suffix)
        assert r['gate_sha256']==hashlib.sha256((OUT.parent/'leangate_imports.py').read_bytes()).hexdigest()
    proof_hashes[sp.name]=sh; proof_hashes[pp.name]=ph
    verdict='ENGLISH_STRONGER' if n==2 else 'EQUIVALENT'
    rows.append(f'| {n} `{name}` | {verdict} | [claim PASS]({cid}.receipt.json), [witness PASS]({cid}.witness.receipt.json) | {notes[n-1]} |')
report='''# Blind g2n1: Phase B results

All ten Phase-A hashes matched. Every back file compiled as written, without repairs. Byte-identical typed copies and their hashes were saved **before** any original declaration was opened. Compilation logs are in `compile-logs/`, no-change records in `compile-fixes/`, and the pre-comparison freeze is [typed/HASHES.json](typed/HASHES.json). No git command, download, or edit to `ControlStack/` was used.

| Claim | Verdict | Receipts | Note |
| --- | --- | --- | --- |
'''+ '\n'.join(rows)+'''

Nine claims have gated pointwise equivalence. Claim 2 has a gated one-way structural comparison and a strict hypothesis-domain extension; it is **not** an equivalence verdict. Every saved statement and both proof targets passed the deterministic gate, with only permitted standard axioms (`propext`, `Quot.sound`, and, for the claim-5 witness, `Classical.choice`) in the reports. A PASS certifies the exact saved `Claim` or `Witness`, not every sentence in this report.

## What the comparison proves

The original declaration types are captured in [ORIGINAL-DECLARATIONS.md](ORIGINAL-DECLARATIONS.md), with source locations; source hashes are in [ORIGINAL-SOURCES.json](ORIGINAL-SOURCES.json). The saved statements copy the frozen Back definition verbatim inside the gate namespace, identify its parameterized form by definitional equality, and compare `BackAt` with the original conclusion `OrigAt` for the same parameters and hypotheses. The safety claims additionally prove the English's expanded predicate iff `Good` on **arbitrary states**, including unsafe states. These proofs use predicate definitions, not proofs of the original safety theorems. Thus equivalence is not manufactured by proving two closed true propositions.

Claim 2 requires a scope qualification. Its original declaration has initial state `⟨files, [], false⟩`; the frozen Back quantifies over `⟨files, [], halted⟩` for arbitrary `halted`. The gate proves Back → Orig by specializing the supplied Back hypothesis at `false`, and a pointwise iff on that original slice. It separately proves original-domain inclusion in the Back domain and strictness at `full, true`. Finally, it tests the coverage direction against an arbitrary conclusion predicate `Q`: broader coverage entails original coverage, but the converse coverage schema fails (take `Q` to be the original domain). **ENGLISH_STRONGER here means strictly broader parameter/hypothesis coverage.** It does not assert a counterexample to safety or the false claim that the two closed safety propositions cannot imply one another in Lean. No original conclusion exists for the extra initial-`true` parameter case in this declaration; establishing its safety would be a further theorem. This distinction is the point of a one-to-one comparison.

For claim 5, `r.caps ⊆ q.caps` unfolds to `∀ c ∈ r.caps, c ∈ q.caps`. The swapped order of `q` and `keep` is harmless once corresponding parameters are aligned. The separate witness constructs a genuine new child with nonempty capabilities, and also shows `[7,7] ⊆ [7]` while `[7,7]` is not a sublist of `[7]`. This distinguishes the theorem's predicate from a count-sensitive reading, without claiming the actual filtering step duplicates capabilities.

For claim 7, the expanded predicate includes **both** the version index and the recorded policy value: `versions[i]? = some (d.val,w)`, `w ∈ admins`, and `i+1 = d.curLen`. The temporal cut is the store length recorded when the decision happened, rather than the final store length. The pinned digest hypothesis is preserved exactly. Claim 8 retains that same hypothesis rather than silently dropping it.

## Hostile reading of “Does NOT say”

| Claim | Assessment of excluded over-readings |
| --- | --- |
| 1 | (1) Respected: only `ran` is quantified, with no real-loader mediation theorem. (2) The missing-interpreter-list caveat is substantively right, but “runs any script” overstates the record semantics: unrecognised binaries ignore the script argument and record `none`. The gated witness exhibits this. (3) Respected: allowlisting proves neither harmlessness nor usefulness; the useful witness is just one configuration. |
| 2 | (1) Respected: `Sound` requires only digest/script checks for this property, with no conclusion about real noexec/halt needs. (2) Respected: digest membership, not path identity, is tested. (3) Respected: hashing and loading are abstract, with no world premise proved. Initial halt scope needs the correction below. |
| 3 | All three respected: halted is a hypothesis, no halt liveness is established, past run records are preserved, and equality concerns only the model state. The witness has nonempty files and past runs. |
| 4 | All three respected: grants can provide capabilities; elevation rules are arbitrary trusted entries and do not require lineage-specific entitlement; kernel bypass and complete recording are not proved. Admin identity is a number supplied by an operation. |
| 5 | All three respected: this is one spawn step; it does not prevent later grants; its hypotheses exclude missing parents and reused child identifiers. “Sub-collection” needs a membership-based definition. |
| 6 | All three respected: no halt liveness, no real process termination or capability removal, and no statement about operations outside the model. The witness preserves nonempty processes, grants and use records. |
| 7 | All three respected: builds append the pinned location, whose digest is exactly the `hpin` premise; full ignores search-path choice for builds; no host mounts, real filesystem, or benign compiler semantics are modeled. The witness sets the search-path tool to 666 but records build 40. “Cited” should explicitly include the policy value. |
| 8 | All three respected: stored values are opaque numbers, writers are claimed caller numbers, and admin-written values need not be correct. The non-admin write in the witness is refused. No mount-table theorem follows without a world mapping to this store. |
| 9 | All three respected: no halt liveness or real firewall guarantee; no in-flight cancellation; equality concerns the abstract state. The witness preserves existing versions, decisions and builds. |
| 10 | All three respected: `registryOnly` models refusal of bypass creation, rather than proving real creation-path completeness; prior effects are not undone; real revocation effectiveness is not established. The witness includes an ignored spawn claim, a refused bypass, one pre-end firing and no post-end firing. The hypothesis prose incorrectly gives bypass attempts claimed labels. |

## Corrections to the English

Replacement text only; no input/part file was edited.

1. **Claim 2 — initial state.** Replace “The same safety statement … from any initial files with no runs” and its hypothesis description with: “For any environment and checks with digest checking and script checking on, start with arbitrary files, an empty run list, and the halted flag set to false. After any trace, every recorded run has an allowlisted program digest and every listed-interpreter run has an allowlisted script digest. The noexec and halt switches may have either value.” This matches the named original declaration. If either initial halted flag is intended, name and prove that extension separately.

2. **Claim 1 — missing interpreter entry.** Replace “an allowlisted interpreter missing from that list runs any script” with: “If an allowlisted binary's digest is missing from the interpreter list, the model treats it as a non-interpreter, does not check its supplied script argument, and records the run with no script. This does not establish what a real interpreter executes.”

3. **Claim 5 — sub-collection.** Replace its conclusion with: “Every newly appearing process has the parent's lineage, and every capability value in its capability list occurs in the parent's capability list immediately before this spawn step. The subset predicate is membership inclusion; it does not compare occurrence counts or list order.”

4. **Claim 7 — policy content and time.** Replace the decision clause with: “Every recorded decision stores a policy-version index and the value at that index; the version's writer is on the admin list, and its index plus one equals the store length recorded when that decision was made.” Keep the separate pinned-digest build clause and its hypothesis.

5. **Claim 10 — bypass arguments.** Replace “including arbitrary claimed session labels for spawns and bypass attempts” with: “including arbitrary claimed session labels for registered spawns; bypass attempts carry a parent, child identifier and job flag, but no claimed session label.”

## Ambiguities exposed

- **Claim 2:** “same safety statement” can inherit claim 1's initial `false`, while “with no runs” suggests arbitrary initial halt flags. Phase A explicitly chose the latter. The original declaration resolves the scope to `false`; the frozen Back was not revised after seeing it.
- **Claim 5:** “sub-collection” can mean membership inclusion, multiplicity inclusion, or an order-preserving sublist. Phase A chose membership inclusion and this matches the original. The implementation's filter has additional behavior that should not be substituted for the named theorem's predicate.
- **Claim 7:** “cited” can suggest a version label without matching its policy value; the formal predicate also checks the value. “Latest” means latest at the decision's recorded cut, not latest after the entire trace. “Pinned location” and “digest” are numbers and a function in this abstraction.
- **Claims 4, 8, 10:** admin identities are operation-supplied numbers. The English explicitly warns about this for claims 4 and 8; claim 10 would benefit from the same warning. This is an external authentication limitation, not a mismatch in the compared main predicate.
- **Claims 3, 6, 9:** “frozen” means exact state equality, including preserving existing records. It neither repairs unsafe prior state nor terminates anything in a real OS.

## Reproduction and limits

From the repository root run:

```sh
python3 docs/lean-english/one-to-one/blind-g2n1/regate.py
```

The script requires all ten statement/proof pairs, rechecks every statement, gates `claim` and `witness` separately using proofledger's deterministic gate, rewrites only the twenty JSON receipts, and returns nonzero on any failure. Temporary gate check files are created inside this output directory and removed by the gate. No existing receipt or gate temporary directory is needed. It uses the project root and the four scenario imports configured in [run_gate_blind.py](run_gate_blind.py). It neither generates statements nor accepts earlier PASS receipts as evidence.

The copied runner changes only the relocated output/path resolution, the input glob and `PL_IMPORTS`; [run-gate-relocation.diff](run-gate-relocation.diff) records those edits. Root and helper references require adjustment because the copy is one directory deeper. The gate implementation itself, including banned tokens and nonce/axiom checks, is untouched. Historical failed and intermediate receipts are retained under `attempts/`; only the root-level receipts correspond to final files. In the initial failing run, proof errors caused a nonzero exit; no equivalence verdict was assigned then.

The clean rerun is recorded in [clean-regate-check.json](clean-regate-check.json); final saved Lean-file hashes are in [PROOF-HASHES.json](PROOF-HASHES.json). Statements and proofs are human-authored comparisons whose fidelity to the original declaration types is documented above; the gate certifies those saved propositions, not the correctness of a natural-language interpretation or the real defensive system.
'''
(OUT/'RESULTS.md').write_text(report)
(OUT/'PROOF-HASHES.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':proof_hashes},indent=2)+'\n')
clean=json.loads((OUT/'clean-regate-check.json').read_text())
assert clean['exit_code']==0 and clean['persistent_changes_only_receipts']
start='2026-10-13T04:10:52+00:00'
now=datetime.datetime.now(datetime.timezone.utc)
progress=f'''# Phase B progress

Done: 10/10 unchanged back files compiled; all Phase-A hashes verified; 10 typed copies frozen before originals were read; 10 pointwise/domain comparisons saved; all 10 claim targets and all 10 non-vacuity witnesses passed proofledger's deterministic gate; hostile English review and replacement sentences completed; copied gate runner and clean-state regate validated.

Verdicts: 9 EQUIVALENT; 1 ENGLISH_STRONGER in parameter/hypothesis coverage (claim 2). No closed-true-proposition equivalence argument was used.

Time: first back-compilation stage began around 2026-10-13 04:10 UTC; typed hashes were frozen at 04:11:26 UTC. Completed {now.isoformat()}. Gate receipts contain final hashes and axiom reports.

Not done: none of the requested Phase B artifacts. No input English or original Lean file was changed.

What could not be certified: real-world mediation, authentication, kernel enforcement, digest/loading integrity, physical revocation, host mount configuration and compiler harmlessness remain outside these models. Claim 2's extra initial-true scope is not a case covered by the named original declaration; its verdict is a strict scope comparison, not a safety-failure witness or an assertion that a converse between two closed true theorems is false.

Historical failures: initial proof files lacked witness unfolding and a proof-namespace open; the gate rejected them and regate exited 1. These were repaired only in comparison proof files. No back/typed repair was needed. Final clean-state regate exited 0 and changed only receipts.

Reproduce: `python3 docs/lean-english/one-to-one/blind-g2n1/regate.py` from the repository root.
'''
(OUT/'PROGRESS.md').write_text(progress)
print('Final report written; all 20 current receipts verified against final saved Lean files.')
