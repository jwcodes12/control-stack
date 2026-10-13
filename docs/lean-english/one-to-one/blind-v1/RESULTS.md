# Blind Phase B results

Eight frozen Phase A files were checked against their original declarations. All eight failed standalone compilation because they omitted imports. Adding only the two project imports already named by the supplied gate driver made every file compile; no declaration body changed. The eight original hashes matched `back/BACK-HASHES.json`. Repaired hashes were frozen in `typed/HASHES.json` at **03:33:48 UTC**, before original declarations were first opened at **03:33:58 UTC** on 2026-10-13. Repairs and both compilation logs are retained.

| Claim | Verdict | Gate receipt files | One-line note |
| --- | --- | --- | --- |
| 1 — `Accepted` | **ENGLISH_STRONGER** | [comparison](b1_1.receipt.json), [witness](b1_1.witness-receipt.json) | Back → Orig proved; an accepted reviewer/approver ID collision refutes Orig → Back. |
| 2 — `exclusive_sink` | **EQUIVALENT** | [comparison](b1_2.receipt.json), [witness](b1_2.witness-receipt.json) | Same authority-edge conclusion under exactly the same hypotheses. |
| 3 — `database_custody` | **EQUIVALENT** | [comparison](b1_3.receipt.json), [witness](b1_3.witness-receipt.json) | Same receiver-or-broker disjunction, including its ordering. |
| 5 — `agent_not_receiver_uid` | **EQUIVALENT** | [comparison](b1_5.receipt.json), [witness](b1_5.witness-receipt.json) | Same inequality between the agent and receiver UID fields. |
| 12 — `accepted_no_avoided_path` | **EQUIVALENT** | [comparison](b1_12.receipt.json), [witness](b1_12.witness-receipt.json) | Same two negated avoided-path propositions; zero-step paths are included. |
| 16 — `deployment_broker_safe` | **EQUIVALENT** | [comparison](b1_16.receipt.json), [witness](b1_16.witness-receipt.json) | Same five conclusions with extraction and publication refinement as hypotheses. |
| 20 — `halted_absorbing` | **EQUIVALENT** | [comparison](b1_20.receipt.json), [witness](b1_20.witness-receipt.json) | Same halted flag and release-count preservation for one step. |
| 23 — `runtime_trace` | **EQUIVALENT** | [comparison](b1_23.receipt.json), [witness](b1_23.witness-receipt.json) | Identical concrete Trace proposition with cap 2 and endpoint `s10`. |

## What the gate certified

Each `b1_<n>.statement.lean` and `.proof.lean` is retained with statement-check logs, comparison gate logs, and separately gated witness logs. The helper is a byte-identical copy of the permitted `leangate_imports.py`; banned-token checks, kernel compilation, nonce-based axiom reports, and permitted axioms are unchanged. `GATE-PROVENANCE.json` records its hash. The copied driver changes its input glob to `b1_*`; relocation puts outputs in `blind-v1` and requires correcting the root parent index to keep `PL_LEAN_PROJ` at the repository root. `run_gate_blind.diff` records that path adjustment. No original declaration was edited.

For theorem claims, `OrigConclusion` transcribes the original conclusion and `BackConclusion` transcribes the frozen blind conclusion with fixed parameters. The `Shape` conjunct is proved by definitional reflexivity, checking that the original blind predicate has exactly the displayed quantifiers, hypotheses and conclusion. The other conjunct states the pointwise `BackConclusion ↔ OrigConclusion` under those hypotheses and is also proved by definitional reflexivity. An `original_type` theorem checks the original declaration against the displayed original type. **Neither original theorem truth nor blind theorem truth is used to prove the pointwise equivalence.** Claim 23 has no hypotheses; its two propositions are the same Trace expression, so reflexivity applies directly. Concrete witnesses establish satisfiable hypotheses; claim 16's witness has one published nonce, and claim 23's endpoint has two releases.

For claim 1, the gated Claim states `(∀ d, BackAccepted d → Accepted d) ∧ (Accepted collision ∧ ¬ BackAccepted collision)`. This certifies the direction and a strict separating instance; it does not assert the false equivalence. `collision` keeps `clean`'s edges, agents, broker, receiver, and target IDs, but its reviewer and approver records are respectively:

```text
(id=6, uid=23703, agent=false, privileged=false, hostNetwork=false, role=3, runtimeMatch=true)
(id=6, uid=23703, agent=false, privileged=false, hostNetwork=false, role=4, runtimeMatch=true)
```

All six original groups pass. The original identity check is guarded by `a.id ≠ b.id`, so it imposes nothing on this pair. The blind identity check is guarded by `a ≠ b`; the role difference makes the records unequal, and their equal UIDs violate its broker/receiver exception. This is a model counterexample, not evidence about a deployed system. The directional verdict concerns the frozen blind reading of “distinct nodes”; that English phrase itself admits an ID-based reading.

The directional proof also checks that the changed agent-count filter agrees with the role-0 filter, that the blind writer-source lists imply the original writer checks, and that the omitted start-membership obligation follows from the definition of `reachable`. Those differences do not obstruct Back → Orig.

## “Does NOT say” audit

| Claim | Audit |
| --- | --- |
| 1 | (a) The implementation/kernel limitation is respected, but “edges … are not examined further” is too broad: mediation cuts off reachability, while all edges still undergo the unknown-edge check and applicable writer checks. (b) Missing edges remain invisible; unlisted real edges are not quantified by the predicate. (c) The check fixes six **list entries** and role counts, not six distinct IDs. |
| 2 | (a) Respected: no unconditional real-process guarantee. (b) Respected as statement scope: this conclusion filters on authority, although the stronger all-edge fact follows separately from `Accepted.writers`. (c) Respected: no content claim. |
| 3 | (a)–(c) Respected: receiver/broker sources are allowed, the statement concerns IR edges, and it identifies neither the actual writer nor its content. |
| 5 | (a) Respected: only UID fields are compared. (b) Respected: no broker/receiver UID separation is concluded. (c) Respected as statement scope: no agent-to-agent comparison appears here. `Accepted` separately constrains equal UIDs for nodes with different IDs. |
| 12 | (a)–(c) Respected: the relation excludes steps landing on broker/receiver, includes only listed edges, and has no independent account of other channels. |
| 16 | (a) Respected: the used approval record conclusion contains no signer, digest, destination or review predicate. (b) Respected: publication is assumed, not derived from runtime bytes. (c) Respected: the stated bound is the shared cap, not a per-agent lease-budget conclusion. |
| 20 | (a)–(c) Respected as the scope of this theorem's conclusion: only two fields are advertised, no liveness is asserted, and the admin-only halt rule belongs to the model. “Does NOT say” should not be read as saying no stronger fact could be derived by examining the transition constructors. |
| 23 | (a)–(d) Respected: the statement is a concrete model Trace, not a runtime-authenticity, clock, completeness or sink-files theorem. The identity denial step imposes no denial-reason guard. |

The over-reading audits inspect the supplied English and original Lean statements/definitions. They do not validate extraction, runtime logs, Python, the kernel, or deployment behavior.

## Corrections to the English

1. **Claim 1, identities — replace “distinct nodes” with:** “For any two entries in `d.nodes` whose **IDs differ**, their UID fields are equal if and only if their IDs are the broker and receiver IDs, in either order. Entries with the same ID are exempt from this identity check.” This removes the ambiguity that produced the strict blind reading.
2. **Claim 1, role counts/topology — replace “There are exactly six nodes” with:** “The node list has length six, with two role-0 entries and one entry for each of roles 1–4; the stated flag and broker/receiver ID equivalences also hold. These checks do not require all six node IDs to be distinct.” Replace “fixes the topology to exactly six nodes” with “fixes the node-list length and role counts to this six-entry, two-agent slice.”
3. **Claim 1, writers — replace the set/list wording with:** “Counting list entries, the sources of write edges into the sink form exactly the singleton list `[receiver]`. There are exactly two write-edge entries into the database, including a broker-source entry and a receiver-source entry; their list order is irrelevant.” This states multiplicity explicitly.
4. **Claim 1, Does NOT say (a) — replace the mediation sentence with:** “The avoided-path computation stops when an edge would land on the broker or receiver. Listed edges still undergo the basic and applicable writer checks; the broker's and receiver's actual forwarding behavior is outside this predicate.”
5. **Claim 1, decidability note — replace “its decidability instance is by infer_instance” with:** “Each finite check group is decidable; the `Accepted` instance uses `decidable_of_iff` to assemble those checks into the structure predicate.”
6. **Claim 12, avoided-path explanation — add:** “A zero-step path from the starting ID to itself also counts.” Without that sentence, “a chain of edges” could be read as requiring at least one edge.
7. **Claim 5, operating-system gloss — clearer replacement:** “Every agent node's UID field differs from the UID field of any listed receiver node; interpreting that as a fact about process identities requires faithful UID extraction.” The batch already supplies that world premise; this keeps it next to the claim.

No part file or input batch was edited. Claims 2, 3, 16, 20 and 23 need no substantive replacement of their main sentences.

## Ambiguities the blind formalisation exposed

- **Record inequality versus ID inequality:** the consequential mismatch in claim 1. The original has no global ID-uniqueness check. Even its reviewer and approver may share an ID and UID in an accepted model instance.
- **Sets versus lists:** original writer checks count duplicates. The blind form selected list multiplicity and made database source order irrelevant. Its implication to the original is gated; word “set” should be removed.
- **What “exactly six nodes” counts:** list length and role counts need not mean six distinct service identities.
- **Reachability includes its starting point:** the blind predicate omitted explicit start membership; the directional proof derives it from the fold's preservation of previously seen IDs. It is redundant, unlike the identity distinction.
- **“Does NOT say” describes stated conclusions:** some stronger model facts follow from `Accepted` or transition constructors. These caveats are not proofs of logical independence from all hypotheses.
- **Order and clock in claim 16:** publication is a reversed sublist of consumed nonces, indexed in admission order. It supplies neither authentic wall-clock ordering nor runtime completeness. The existing wording “in admission order” is appropriate.
- **The blind theorems retain the real `Accepted` premise:** their seven equivalence verdicts compare theorems conditional on that original predicate. They do not repair, or silently inherit, claim 1's reconstructed definition.

Failed attempts are retained under `attempts/`. They are not verdict evidence. In particular, gate failures containing elaboration-generated `sorryAx` were rejected; final successful receipts permit only the standard allowed axioms. No `native_decide`, added axiom, or weakened security check was used.
