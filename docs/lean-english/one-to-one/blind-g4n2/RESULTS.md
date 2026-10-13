# Blind g4n2 Phase B results

All ten saved Claim proofs and all ten Witness proofs passed the deterministic gate in a run started with no receipts and no gate scratch directory. Each receipt contains separate statement, Claim and Witness results and the statement/proof hashes. EQUIVALENT means equivalence of conclusions with parameters and model hypotheses aligned; it does not mean two closed theorems were merely proved true.

| Claim | Verdict | Receipts | Note |
|---|---|---|---|
| 1: `SC18Refinement.concrete_safe` | EQUIVALENT | [Claim + Witness](bg4n2_1.receipt.json) | Equivalent on runs from cinit; the omitted acknowledgement-count bound follows from a separately proved structural invariant. |
| 2: `SC18Refinement.concrete_durable` | EQUIVALENT | [Claim + Witness](bg4n2_2.receipt.json) | Identical prefix-ack membership, sink-log membership and release-time inequality. |
| 3: `SC19.sc19_safe` | EQUIVALENT | [Claim + Witness](bg4n2_3.receipt.json) | Identical Good predicate on every state; verifier-role provenance is supplied by the reachable model, not recorded in Good. |
| 4: `SC19.halt_freezes` | EQUIVALENT | [Claim + Witness](bg4n2_4.receipt.json) | Identical state equality under the same halted hypothesis, including arbitrary unreachable starting states. |
| 5: `AuthInstances.sc19_safe_authenticated` | EQUIVALENT | [Claim + Witness](bg4n2_5.receipt.json) | Provenance witnesses normalize to the same approval/verification facts; predicate/list sets agree on finite trace support. |
| 6: `AuthInstances.forged19_destroys_without_auth` | EQUIVALENT | [Claim + Witness](bg4n2_6.receipt.json) | Identical concrete destruction record and authenticated empty result; compared as predicates of arbitrary output lists. |
| 7: `SC20.sc20_safe` | EQUIVALENT | [Claim + Witness](bg4n2_7.receipt.json) | Identical digest-level Good predicate on every state; no source, writer distinction or frozen-content equality added. |
| 8: `SC20.halt_freezes` | EQUIVALENT | [Claim + Witness](bg4n2_8.receipt.json) | Identical state equality under the same halted hypothesis, including arbitrary unreachable starting states. |
| 9: `AuthInstances.sc20_safe_authenticated` | EQUIVALENT | [Claim + Witness](bg4n2_9.receipt.json) | Provenance witnesses normalize to the same promotion facts; predicate/list sets agree on finite trace support. |
| 10: `AuthInstances.forged20_trains_without_auth` | EQUIVALENT | [Claim + Witness](bg4n2_10.receipt.json) | Identical training result and authenticated empty result; compared as predicates of arbitrary output lists. |

## Evidence and comparison method

All ten Phase A files matched [BACK-HASHES.json](back/BACK-HASHES.json). Each was compiled as written before repair; all failed because they lacked imports. Each final repair adds exactly one project import and leaves the proposition body unchanged. The [compile-fixes](compile-fixes/) directory contains the ten no-meaning-change diffs, raw compilation logs and successful typed compilation logs. [typed/HASHES.json](typed/HASHES.json) was written with all ten successful compilation results before any original declaration was opened. Import discovery used module filenames and compilation diagnostics: AuthInstancesB did not supply SC19 names, and AuthInstancesA did not supply SC20 names. These failed import candidates were replaced before the final freeze.

Original theorem headers and source hashes are saved in [originals/HEADERS.json](originals/HEADERS.json) and the adjoining declaration files. Each saved statement includes its frozen back definition verbatim, without its import line. In each proof, `back_shape` establishes by reflexivity that BackPoint reconstructs that exact back definition. `original_type` makes Lean check the copied OrigPoint against the original declaration's conclusion. The equivalence proofs do not use `original_type` or the original safety theorems as evidence for either side of the iff.

- **1:** Claim is `∀ T ops, BackPoint T (runC real T cinit ops) ↔ OrigPoint T (runC real T cinit ops)`. OrigPoint unfolds `Resume.RelOk`, which additionally requires `r.llen ≤ logged.length`. `len_step` and `len_run` prove that count bound by induction using only the machine's append rules, independently of safety. The forward direction combines that structural bound with the assumed Back conclusion; the reverse direction projects the same membership and timing facts. No truth-of-theorem shortcut is used. An additional Lean counterexample shows that equivalence fails on arbitrary fabricated states: one ack with a reply recording `llen = 2` satisfies BackPoint but fails OrigPoint. Such a state cannot be produced by these runs.
- **2:** BackPoint and OrigPoint are definitionally identical for every T and concrete state. Substituting the same `runC real T cinit ops` reconstructs both declarations.
- **3 and 7:** BackPoint and OrigPoint both use precisely the original Good predicate, with an iff proved for every environment and every state. Substitution of `run E full init ops` reconstructs the theorem instances. SC19 Good's verified-index membership does not itself record a verifier identity; permitted verify events in the reachable model supply that reading. SC20 Good admits precisely registry digests or promoted digests with a listed reviewer.
- **4 and 8:** The iff compares `run E full s ops = s` under the same `s.halted = true` hypothesis, for arbitrary states. It adds no reachability assumption.
- **5 and 9:** The provenance iffs are proved even for arbitrary final states and arbitrary traces, by eliminating or introducing the original existential issuer and operation witnesses. No authentication safety theorem proves the equivalence. `U : List Nat` is interpreted as its membership predicate, making the disjointness premises identical. The gated Claim also proves that an arbitrary predicate U can be restricted to the issuers appearing in the finite trace, giving a list V with `V ⊆ U` and the same pointwise conclusion. Hence inherited disjointness is preserved, and no infinite-set advantage is silently assumed. The operation equalities match the same recorded approver/reviewer and record id; SC19 verification keeps the same snapshot index.
- **6 and 10:** The iffs range over arbitrary unauthenticated and authenticated output lists. Both predicates demand the same exact result lists. They are specialized to the same environment, claim mappings and forged traces by `back_shape` and `original_type`. Witnesses independently compute the concrete runs with kernel-checked `decide`.

Witnesses are nonempty: Claims 1/2 release a reply; 3 destroys five objects; 4/8 start halted with existing objects/data and attempt further operations; 5 has an authenticated destruction plus approval and verified snapshot with nonempty adversary set [1] disjoint from both roles; 7 trains a reviewed example; 9 trains with an authenticated promotion and nonempty adversary set [1] disjoint from reviewers; 6/10 compute the stated successful unauthenticated effects and blocked authenticated effects.

## Corrections to the English

No claim requires a change of mathematical verdict under its stated model and initial-state hypotheses. The following replacement sentences would remove omissions or make the statement more directly match the original conclusion. They are proposals only; no input or part file was edited.

**Claim 1 — make the acknowledgement prefix and its count explicit:**

> For every T and every event list run from cinit with real flags, each released reply r records an acknowledgement count r.llen no larger than the final proxy acknowledgement-list length; its id belongs to that list's first r.llen entries; its recorded release clock is at most r.lastAck + T, where r.lastAck is the last record-ack clock recorded at release; and released request ids are distinct.

The extra count clause is redundant for these runs, as the gated structural induction proves. It is not redundant if the property is applied to arbitrary states. Claim 2 can use the same explicit description of `r.lastAck` to avoid confusing its historical value with the final state's acknowledgement clock.

**Claims 5 and 9 — specify the representation of U:**

> Let U be a list of adversary-controlled issuer ids, interpreted through membership; assume it is disjoint from the listed trusted roles.

An abstract set formulation also works for the finite traces, by the gated finite-support adapter. This is a precision edit, not evidence that predicate sets invalidate the English. Duplicates or order in the original list have no effect on its membership-based premises or conclusions.

**Claim 3 — distinguish the safety predicate from verifier provenance:**

> Each destroyed record has a matching-target, matching-version snapshot whose index is in the final verified-index list; from the initial state, only a caller listed in E.verifiers can append such an index.

This keeps the correct reachable-state reading while making clear that Good stores a verified index, rather than a verification record naming its issuer. Neither formulation proves a restore test passed.

**Claim 7 — state precisely the final-state digest predicate:**

> For every content entry q in every final training-run record, E.registry q.id equals some (E.h q.content), or the final promotion list contains a record for that id and digest whose recorded reviewer belongs to E.reviewers.

“Made by a caller” is supported by the reachable step rules; the conclusion itself is membership in a final log with a listed reviewer. Avoid adding a source, writer-distinctness, timestamp, actual-content equality, or cleanliness assertion to this sentence.

**Claim 10 — make the concrete environment self-contained if desired:**

> In E0, the allowlist is [50], the reviewer list is [2], the admin list is [9], h is identity, and the registry returns some 7 at id 0 and none at every other id; on the stated forged trace, ignoring claims records exactly [[(1, 66)]], while checking claims records no training run.

The omitted registry details do not change this agent-written example's behavior, but naming E0 alone leaves a reader dependent on another declaration.

## Ambiguities exposed

The English caveats were checked against the declarations, supporting definitions and model guards. They are respected as follows:

| Claim | Hostile reading of “Does NOT say” |
|---|---|
| 1 | All three exclusions are respected. This is a model transfer, with id-level acks and an assumed prompt-release guard. It proves no Python implementation link, runtime scheduling guarantee, digest/body match, attacker authentication, configuration integrity, real latency or single release path. Pings refresh a different concrete clock; r.lastAck retains the record-ack clock at release. The within-T clause is an upper bound in model ticks. |
| 2 | All three exclusions are respected. Sink-log membership concerns the model's list and modeled ack-after-commit rule; there is no physical-durability, tamper-evidence or configured trusted-sink theorem. Its timing premise is the same prompt-release guard. |
| 3 | All three exclusions are respected. Verified means a permitted caller appended an index. Approver ≠ author compares natural-number identities, and every represented write is versioned. Restore success, genuine human separation, outside effects and a physical blast-radius bound are absent. |
| 4 | All three exclusions are respected. Every represented operation is frozen on a halted state, including writes and snapshots. This asserts neither external-writer control, timely halting, authenticated administrators nor coverage outside the machine. The input state need not be reachable. |
| 5 | All three exclusions are respected. Good transfers to an authenticated subtrace independently of role-disjointness; authentication adds issuer provenance. True-issuer attachment and adversary-role disjointness are assumptions. Listed principals need not be honest or careful. Write/snapshot/commit have no claimed identity to check. |
| 6 | All three exclusions are respected. This is one fixed computed trace, not a platform theorem or a general necessity result. Both verify and approve are forged; the conjunction does not isolate either forgery. |
| 7 | All three exclusions are respected. Good contains no cleanliness or label predicate, allowlist membership, reviewer/writer inequality, or equality of current and frozen content. Registry and reviewers are trusted within the model. Arbitrary h may collide. A recorded run can be empty. The caveat correctly distinguishes the weaker conclusion from stronger freeze/promotion guards. |
| 8 | All three exclusions are respected. Halt is absorbing for every represented operation, including edits and ingestion, but establishes no control of real external writers, timely/authenticated halting, or safety of earlier training. No Good hypothesis is required. |
| 9 | All three exclusions are respected. The added conclusion is an issued promote operation matching the record's id and reviewer, with that issuer outside U. It contains no digest assertion about the operation itself, honest review, allowlist clause, writer distinction or frozen-content equality. Ingest/edit/train have no claim to authenticate. |
| 10 | All three exclusions are respected. The example checks both forged promote and forged freeze; lack of an accepted freeze already prevents training. It gives neither a general promotion-isolation result nor real-platform authentication. |

The substantive issues are the omitted count bound in Claim 1, predicate/list representation in 5/9, historical-versus-final acknowledgement clocks in 1/2, and the distinction between stored final-state facts and real-world provenance or semantic guarantees. The gated proofs resolve the first two for the requested comparisons. The remaining caveats are limits of the modeled conclusions, not failed equivalences.

## Reproduction

From the repository root:

```sh
python3 docs/lean-english/one-to-one/blind-g4n2/regate.py
```

This reads the saved statements/proofs and imports/paths from [run_gate_blind.py](run_gate_blind.py), invokes the unchanged deterministic gate for every statement and then separately for Claim and Witness, rewrites only the ten receipt files, and exits nonzero if any check fails. Its temporary Lean files are removed by the gate; it can recreate an absent scratch directory. Python bytecode writing is disabled before loading the gate helper, so no cache is written outside this directory. No generated olean or local back-file imports are required.

[run_gate_blind.diff](run_gate_blind.diff) records the copied runner's import list, claim glob and directory-relative relocation changes. The project root and helper path were adjusted because the copy is one directory deeper. The banned-token scanner, nonce-bound theorem construction and axiom allowlist remain unchanged in the allowed helper. [CHECK-HASHES.json](CHECK-HASHES.json) identifies the final saved statements and proofs.
