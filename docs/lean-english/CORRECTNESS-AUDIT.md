# Correctness audit — all 26 G0 claims and new PR Lean work

**Model-written and model-reviewed; no independent human review.** The earlier G0 comparison was not strictly blind. This statement-level audit does not confer a verified badge.

Each row records (a) joint hypothesis satisfiability with a witness, (b) whether the conclusion is substantive or projected from an assumption, (c) axiom status and (d) what is not claimed.

**Axiom status for all rows: PENDING exact per-claim dependency extraction.** Existing Lean #print and pinned CI are not a substitute for inspecting each specific elaborated declaration. This flag does not mean nonstandard axioms were found.

## G0 (26 claims)

| # | Declaration | Hypotheses: witness or gap | Conclusion vs hypothesis | Axioms | Not claimed |
|---|---|---|---|---|---|
| 1 | Accepted | clean_accepted | Definition, not theorem; bundling original checks | Pending per-claim report | Cannot prove real inventory truthful |
| 2 | exclusive_sink | Witnesses.sink_positive | Restatement of BaseAccepted field | Pending per-claim report | Only authority-labelled IR edges |
| 3 | database_custody | Witnesses.database_positive | Restatement of BaseAccepted | Pending per-claim report | Broker OR receiver may access database |
| 4 | runtime_exclusive | Witnesses.runtime_positive | Transport via assumed Faithful extraction | Pending per-claim report | Does not establish faithful actual extraction |
| 5 | agent_not_receiver_uid | Witnesses.identity_positive | Projection of identity field | Pending per-claim report | Other impersonation means are out of scope |
| 6 | agent_call_legal | Witnesses.legal_call_positive | Projection of UID inequality to SC26 legal op | Pending per-claim report | No real OS peer identity proof |
| 7 | protocol_safe | Witnesses.protocol_positive | SC26 guarded model safety | Pending per-claim report | Not a Python runtime theorem |
| 8 | one_use | Witnesses.one_use_positive | Model nonce uniqueness | Pending per-claim report | A fresh nonce can use the same payload |
| 9 | gate_contract | Witnesses.gate_positive | Model gate trace invariant | Pending per-claim report | Observed effect completeness assumed |
| 10 | broker_contract | Witnesses.useful_broker_trace | Step to trace safety induction | Pending per-claim report | Atomicity and anti-rollback external assumptions |
| 11 | deployment_safe | Witnesses.sc26_refined and extracted | Composed conditional contract | Pending per-claim report | SC26 publication equality assumed |
| 12 | accepted_no_avoided_path | Witnesses.path_positive | Induction from NoBypass closure | Pending per-claim report | Only sink and database IR paths |
| 13 | accepted_path_safety_monotone | clean subset clean, constructible | Path safety only; not Accepted monotone | Pending per-claim report | Missing writers make Accepted false |
| 14 | path_edge_subset | clean identity subset and reflexive path | Structural path transport | Pending per-claim report | No acceptance guarantee |
| 15 | requested_monotonicity_counterexample | sinkOnly vs clean | Concrete countermodel of Accepted monotonicity | Pending per-claim report | Does not refute path-safety monotonicity |
| 16 | deployment_broker_safe | Witnesses.useful_deployment_broker | Combines guarded broker trace and sublist | Pending per-claim report | Exact file digest/destination unproved |
| 17 | indexed_receipts_sound | Witnesses.singleTable | Trace soundness from checked table hypothesis | Pending per-claim report | Empty/truncated transcript accepted |
| 18 | transaction_preserves | initial_safe and Witnesses.staged | Induction over Step constructors | Pending per-claim report | No real SQLite correspondence |
| 19 | transaction_coherent | initial_coherent and Witnesses.staged | Nonce-used coherence induction | Pending per-claim report | Arbitrary corrupt state not covered |
| 20 | halted_absorbing | HALT step from initial, constructible no named witness | Step excludes releases in halted states | Pending per-claim report | No HALT processing liveness |
| 21 | committed_nonce_unusable | Witnesses.replay_refuted | One-use after updating used flag | Pending per-claim report | Fresh nonce replay not blocked |
| 22 | trace_preserves | Witnesses.useful_broker_trace | Induction on serial traces | Pending per-claim report | No concurrent partial OS effects |
| 23 | runtime_trace | TranscriptReplay.runtime_trace | Concrete model witness | Pending per-claim report | Ten steps in proof not theorem type; prior G0 verdict STALE |
| 24 | final_safe | TranscriptReplay.final_safe | Safety from verified model trace | Pending per-claim report | No proof recorded real log complete |
| 25 | replay_was_not_allowed | TranscriptReplay.replay_was_not_allowed | Concrete rejected reused-nonce witness | Pending per-claim report | Only named replay form |
| 26 | omitted_tail_is_accepted | TranscriptReplay.omitted_tail_is_accepted | Negative control of checker completeness | Pending per-claim report | No claim actual truncation occurred |

## PR-added theorem/definition families

| Group | Jointly satisfiable | Restatement or substantive? | What is NOT claimed |
|---|---|---|---|
| NamedContracts iff fields | release_allowed and clean_accepted | Intentional re-expression of 21 broker and 7/6 IR guards | Equivalence does not prove necessity or real enforcement |
| Provenance Step/Trace invariants | Witnesses.useful_broker_trace | Substantive model inductive preservation | Current review/approval facts only, not exact past file bytes |
| Provenance deployment_broker_provenance | ProvenanceWitnesses.approved_publication_provenance | Conditional retained approval and role conclusions | Assumed publication subset; no immutable digest/destination log |
| ProvenanceWitnesses.unreviewed_approval_refutes | unreviewedState | Negative model state not reached by guarded transitions | Not a live exploit |
| GuardNecessity AllowedExcept deletion cases | Witnesses.s4 and mutant states | Five explicit single-guard countermodels; 16 not demonstrated necessary for specified invariant | Nonce witness has Safe but noncoherent prestate |
| GuardNecessity avoided_paths_from_nobypass | clean_accepted.bypass | Projection from NoBypass by induction | No reason to remove other acceptance fields |
| ComposedAssurance accepted_joint_claim | all_hypotheses_satisfiable and witness_combined_nonce_and_provenance | Conditional composition of sink exclusivity, nonce cap and provenance | ExtractionFaithful and BrokerProtocolRefinement still environmental assumptions |
| RefinementTransfer run_simulation | SC25 and SC16 bridge instances | Generic model-to-model trace induction | Not OS/runtime correspondence |
| SC25RefinementReuse via_transfer and agree | Original SC25 simulation | Same conclusion; agree by proof irrelevance | Pinned source not rewritten |
| SC16RefinementReuse via_transfer and agree | Original SC16 simulation | Same conclusion; agree by proof irrelevance | Python code not shown equivalent to model |

All new groups have **axiom status pending per-declaration Lean environment extraction**, even where the source contains #print axioms.

## Flags (do not silently fix)

1. Exact per-claim dependency and axiom extraction remains incomplete (task 4). No claim has been newly verified here.
2. Only five Allowed release-guard deletion countermodels are established, and one uses a noncoherent prestate. Other guards protect properties not expressed in Safe.
3. Broker State has no per-release destination/digest event log; exact publication provenance is not expressible.
4. SC-07, 18, 26, 27 and 28 need additional invariant/legal-trace premises for generic induction.
5. Changed runtime_trace English makes historical G0 result STALE; G1-G7 (161 claims) have never been checked one-to-one.
6. Human review is completely outstanding. Live/privileged container execution and world correspondence are not asserted.

Reproduce: lake build; python3 tools/check_scenarios.py; tools/build_registry.py --check; tools/build_statement_catalog.py --check; tools/build_lean_english_overview.py --check; inspect pinned deployment-release CI on exact head.
