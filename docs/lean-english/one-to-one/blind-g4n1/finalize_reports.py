"""Write final human reports only after all final claim and witness receipts pass."""
from pathlib import Path
import hashlib,json,datetime
OUT=Path(__file__).resolve().parent
validation=json.loads((OUT/'regate-validation.json').read_text())
assert validation['passed']
freeze=json.loads((OUT/'typed/HASHES.json').read_text())
for item in freeze['files'].values():
    assert hashlib.sha256((OUT/item['file']).read_bytes()).hexdigest()==item['sha256']
originals=json.loads((OUT/'original-manifest.json').read_text())
for item in originals['files'].values():
    assert hashlib.sha256((OUT.parents[3]/item['file']).read_bytes()).hexdigest()==item['module_sha256']
base_hashes=json.loads((OUT/'back/BACK-HASHES.json').read_text())
assert all(hashlib.sha256((OUT/p).read_bytes()).hexdigest()==h for p,h in base_hashes['files'].items())
assert (OUT/'leangate_imports.py').read_bytes()==(OUT.parent/'leangate_imports.py').read_bytes()
notes={
1:'Identical hypotheses and Good conclusion. Outage wording needs clarification: an acknowledged request can still be released with the sink down.',
2:'Identical final configuration equality. The legal premise supplies trusted admin behaviour; attempts by non-admins can occur.',
3:'Identical released-list equality. The English clock/tick aside is false: halted ticks leave the state unchanged.',
4:'Predicate U versus list U resolved by a gated finite projection preserving both hypotheses and the conclusion. Real-issuer authenticity remains outside the model.',
5:'Identical concrete conjunction for forged18, with identical numbers and both authentication modes.',
6:'Identical membership conclusion for arbitrary non-halted, sink-up states. Witnesses also show an untrusted config and an earlier unsafe release.',
7:'Append/cons and staged-run presentations normalize to the same pointwise disjunction. Witnesses realize success, halt and sink-down alternatives.',
8:'Identical watchdog premise, strict inequality and final halted flag. Tick operations after halt do not advance the clock.',
9:'The let-bound final state unfolds to the original safety conjunction. Pause/resume witness actually releases a record.',
10:'Identical membership conclusion. A paused state can release; an already released id need not acquire a new or repaired release record.'}
rows=[]
for n in range(1,11):
 cid=f'bg4n1_{n}'
 for target,suffix,proof_suffix in [('claim','receipt.json','proof.lean'),('witness','witness.receipt.json','witness.lean')]:
  r=json.loads((OUT/f'{cid}.{suffix}').read_text());assert r['passed'] and r['statement_check_passed']
  assert r['statement_sha256']==hashlib.sha256((OUT/f'{cid}.statement.lean').read_bytes()).hexdigest()
  assert r['proof_sha256']==hashlib.sha256((OUT/f'{cid}.{proof_suffix}').read_bytes()).hexdigest()
 name=next((OUT/'back').glob(f'{n}-*.lean')).stem.split('-',1)[1]
 rows.append(f'| {n}: `{name}` | EQUIVALENT | [claim]({cid}.receipt.json), [witness]({cid}.witness.receipt.json) | {notes[n]} |')
text='''# Blind g4n1 — Phase B results

All ten **formal back translations** are pointwise equivalent to the original conclusions under the corresponding hypotheses. Every comparison and its separate non-vacuity witness passed the provided deterministic gate. This does **not** certify every explanatory sentence in the English: the false halt/clock aside and other ambiguities are corrected below.

All Phase A hashes matched `back/BACK-HASHES.json`. All ten files were compiled as written before any original declaration was opened. All failed because imports were missing; the only repairs were project imports, recorded as meaning-preserving diffs in `compile-fixes/`. The repaired sources were successfully compiled and frozen in `typed/HASHES.json` before opening the originals. No back file, English input or ControlStack source was edited. No git command or download was used.

Each statement saves the frozen Back definition, `BackAt` and the original conclusion `OrigAt`. `Claim` includes a source-reconstruction iff and an iff **inside the parameter and hypothesis binders**. Comparison proofs do not invoke any of the ten original theorems. Claim 5 compares the identical concrete formulas by reflexivity rather than proving both true. Claim 7 normalizes trace concatenation and fold execution. Claim 4 additionally proves a finite representation of an arbitrary issuer predicate on all admins and trace issuers, preserving both hypotheses; this does not assert that every infinite predicate has a globally equal finite list. `comparison-map.json` and `original-signatures.txt` record the correspondence. Claims 6–8 inherit the module section parameters `admins`, `trusted`, `T`.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
'''+ '\n'.join(rows)+'''

## Corrections to the English

1. **Claim 3, “Does NOT say” (1): replace the whole sentence with:** “The released list is frozen, and the halt flag stays set. With `full`, tick operations in a halted state leave the entire state unchanged, so the clock does not advance. Sink-down and sink-restore operations can still change `sinkUp`.” The separately gated witness starts halted at clock 7, processes a nonempty trace including a tick and attempted release, and finishes at clock 7 with the same nonempty released list and the sink down; it also proves the halted tick leaves the state unchanged.

2. **Claim 1, protection-list wording: replace “fail-closed on sink outage” with:** “no fail-open exception for unacknowledged requests during a sink outage; a watchdog that halts after more than T silent model ticks; and a halt check.” Add: “A sink outage does not immediately forbid releases: a previously acknowledged request may be released before the watchdog halts the node.” Claim 7's gated witness explicitly has `sinkUp = false` and released ids `[0]` after `[request 0, logWrite 0, sinkDown, release 0]` with `full`.

3. **Claim 10, “Does NOT say” (3): replace with:** “This theorem asserts only membership in the final released-id list. For an arbitrary starting state it gives no safety guarantee for existing release records. `resume_safe` gives log and timing guarantees only for runs from `init`.” The gated witness preserves an earlier record whose release clock is 100 and last acknowledgement is 0 at T = 2, while all progress hypotheses hold.

4. **Claims 6 and 10, clarify the main sentence by appending:** “If i was already released, it remains in the list; this conclusion does not require a new release or repair an earlier release record.” Both gated witnesses demonstrate the earlier-release case. Claim 6 also demonstrates a newly released id with an empty trusted log when the arbitrary starting config names an untrusted sink.

5. **Claim 8, clarify “after exactly n tick operations” by appending:** “This counts operations in the trace. After the watchdog halts, additional ticks are ignored; n tick operations need not advance the clock by n.”

6. **Claim 4, remove a possible content over-reading by replacing “every release's record was in the trusted log” with:** “every release's request id was in the trusted log at release time.” Continue to label true-issuer authenticity as an external assumption, rather than an assurance proved by the identity comparison.

## Ambiguities exposed

- **1 — over-readings (1)–(3) respected by the formal core:** only ids are logged, there is no log review/content/tamper guarantee, and ticks supply neither wall-clock bounds nor availability. The saved release log length identifies the trusted-log prefix. The acknowledgement timer is refreshed by any successful log write, including another request. The immediate-outage interpretation of “fail-closed” is unsafe; use correction 2.
- **2 — over-readings (1)–(3) respected:** final trusted configuration permits rejected attempts and trusted admin resets. Admin behaviour is assumed by `legal`; sink trustworthiness and reachability are not conclusions. The witness includes a non-admin attempt, an admin reset and a successful release.
- **3 — (1) is partly false prose:** sink status can change, but halted ticks and the clock do not. The released-list conclusion itself is equivalent. (2) correctly distinguishes absorbing model halt from the asserted runtime behaviour; the runtime assertion is outside this audit. (3) correctly leaves halt triggering to the separate watchdog theorem.
- **4 — over-readings (1)–(3) respected:** legality is retained for non-adversary issuers; the model cannot establish platform identity fidelity or protect against a deceived admin; claim-free operations remain unrestricted. Phase A's NOT_FORMALISABLE comment refers to an independent ground-truth issuer mechanism, not to the model theorem. The list/predicate representation issue is discharged by the gate; arbitrary predicates need no new safety conclusion.
- **5 — over-readings (1)–(3) respected:** exactly one concrete trace, checking only the modeled equality test and its omission. The witness confirms issuer 1, claimed admin 9 and sink 66, and both final configurations.
- **6 — over-readings (1)–(3) respected:** no invariant, trusted-config, safety, interleaving or performance assumption is added. The main wording “leaves i among the released ids” is faithful, but “honest release” can suggest a fresh response even when the id was present already. See corrections 4 and the unsafe/preexisting-release witness.
- **7 — over-readings (1)–(3) respected:** an unrestricted trace and state give a disjunction, not guaranteed service or fairness. Sink-down is tested just before the honest log write, not at the final state or at release. Halt is tested at the final state. Membership can concern an earlier release. Witnesses exhibit all three alternatives, and nonempty interleavings permit release during an outage after an acknowledgement.
- **8 — over-readings (1)–(3) respected:** the invariant is only the displayed clock implication, not the entire SC18 invariant. The theorem alone proves a final halted flag, not release-list equality, recovery or a real-time bound. No acknowledgement is interleaved; halt can precede the last of the n tick operations.
- **9 — over-readings (1)–(3) respected:** a separate model starts from `init`, omits configuration and logs to the fixed trusted sink. Safety does not establish correct runtime pause/resume timing. An admin halt is still absorbing; only the watchdog pause is cleared by a successful log write. Claims about concrete refinement or Python linkage in the explanatory text were not verified in this ten-claim audit.
- **10 — (1)–(2) respected; (3) needs correction 3:** sink-up is a starting hypothesis; the two honest steps are consecutive and no interleaving result is promised. Pause may initially be true and no invariant is required. `resume_safe` cannot be applied to an arbitrary, potentially unsafe starting state merely because the progress hypotheses hold.

The gate helper is byte-identical to the provided `leangate_imports.py`; the import-header patch remains the provided one. `run_gate_blind.diff` records the runner's output relocation, claim glob and trusted module imports. The relocated OUT assignment also corrects the project root for the extra directory level. Banned-token and axiom checks were not changed. Receipts allow only the gate's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The inherited `gate_unmodified: false` receipt field records the existing local imports adaptation; it does not indicate a security-check change.

Reproduce from the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g4n1/regate.py
```

This reads every saved statement, comparison proof and witness proof; it independently checks each statement and gates both targets. It rewrites only JSON receipts, apart from the gate's temporary files which it deletes. It does not call the comparison builder or require existing receipts. Any missing file or failed check gives a nonzero exit. A clean run after removing all 20 receipts, gate scratch and Python caches returned 0 with 20 passing receipts and byte-identical saved inputs; see `regate-validation.json`. Actual earlier runs with failing witness drafts returned 1. Final receipts and their source hashes are authoritative.
'''
(OUT/'RESULTS.md').write_text(text)
completed=datetime.datetime.now(datetime.timezone.utc)
first=datetime.datetime.fromtimestamp((OUT/'compile-logs/1.as-written.txt').stat().st_mtime,datetime.timezone.utc)
progress=f'''# Phase B progress

Done: 10/10 as-written compile attempts; 10/10 import-only repairs and successful recompiles; all Phase A hashes verified; repaired sources hashed before originals were opened; 10/10 pointwise comparisons; 10/10 independently gated non-degenerate witnesses; all 20 final receipts passing; hostile reading of all “Does NOT say” items; replacement sentences; copied gate runner; clean-state regate validation.

Not done: no requested Phase B work remains. English source files were not edited, as instructed. No runtime, platform-authentication, concrete-refinement or Python-to-machine audit was attempted; those are outside these ten formal claims.

Time: typed freeze {freeze['frozen_at_utc']}; clean regate {validation['started_at_utc']} to {validation['completed_at_utc']}; report completed {completed.isoformat()}. Elapsed from the first saved as-written compile result: {(completed-first).total_seconds()/60:.1f} minutes.

What I could not do: formalize or prove platform identity fidelity to an independent real issuer using these model declarations. It remains the English's stated world assumption, not an unfinished comparison. I also cannot certify the runtime assertions in the explanatory prose from these ten declarations. Early comparison/witness proof drafts had elaboration failures; they were repaired without changing any frozen back translation or gate security check. Earlier failing regates exited 1; the final clean regate exited 0.

Verdicts: all ten EQUIVALENT for the formal Back ↔ Orig comparison. This is explicitly separate from the false/ambiguous explanatory prose recorded in RESULTS.md.
'''
(OUT/'PROGRESS.md').write_text(progress)
print('Reports finalized: 10 comparisons, 10 witnesses, clean regate PASS.')
