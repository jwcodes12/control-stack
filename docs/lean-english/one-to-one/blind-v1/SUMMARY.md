# Blind one-to-one re-check of the eight stale G0 claims: summary (2026-10-13)

**Model-written and model-checked; no independent human review.** Sol (`gpt-6.1-sol`) did both phases in separate fresh sessions; the orchestrator (Claude) built the
isolation, audited the logs and re-ran every gate check.

| Claim | Blind verdict | Notes |
|---|---|---|
| 1 `Accepted` | **ENGLISH_STRONGER** | Back → Orig proved; a model counterexample refutes Orig → Back. The English said "distinct nodes"; read as *distinct records* it is stronger than the Lean (which compares *IDs*). |
| 2 `exclusive_sink`, 3 `database_custody`, 5 `agent_not_receiver_uid`, 12 `accepted_no_avoided_path`, 16 `deployment_broker_safe`, 20 `halted_absorbing` | EQUIVALENT | Same conclusion under the same hypotheses, proved through the gate; the equivalence does not rely on both sides being true theorems. |
| 23 `runtime_trace` | EQUIVALENT (weak evidence) | The Phase A excerpt contained the concrete `s10` and roles, so the blind statement restates the theorem; this says little about whether the English determines the data. |

What was done and how to trust it:
- **Phase A (blind):** statements written in `phase-a/` from English plus definition-only excerpts; hashed (`back/BACK-HASHES.json`, 03:30:41 UTC); the command log has 3 commands and the audit flags none (`phase-a/AUDIT.txt`). No toolchain, no originals, no objects were present.
- **Phase B:** every back file failed to compile only for missing imports; adding the two imports changed no declaration body; repaired hashes were frozen (`typed/HASHES.json`, 03:33:48 UTC) before the originals were first opened (03:33:58 UTC; command 14 of 38 in `COMMANDS-phase-b.txt`, hashes at command 10).
- **Gate:** proofledger's deterministic gate with only the import-header option changed (`leangate_imports.py` differs from the proofledger original only by `import_header`/`PL_IMPORTS`); banned-token and axiom checks unchanged. The orchestrator re-ran all 8 comparison and 8 witness gates: all pass, statement and proof hashes identical to Sol's receipts.
- **Caveats:** one model, one run per claim; Sol's equivalence statements are its own transcriptions of the original conclusion (`OrigConclusion`) checked against the original declaration's type by an `original_type` theorem, so the weak point is the back-translation, not the transcription; the excerpt tool, not a person, chose what Sol could see; the English corrections it proposes (`RESULTS.md`, 7 items, mostly about "distinct nodes", list multiplicity, mediated edges and zero-step paths) were **not applied** to the part files, so these blocks remain as written until the owner decides. No badges were added.
- **Not covered:** claims 4, 6-11, 13-15, 17-19, 21-22, 24-26 of G0 (their old verdicts stand as non-blind) and G1-G7 (161 claims, never checked).
