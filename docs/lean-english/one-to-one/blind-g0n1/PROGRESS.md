# Phase B progress

Done: 10/10 claims, each EQUIVALENT after a passed pointwise claim gate. All 10/10 separately gated Witnesses also passed. Every back file compiled as written; all Phase A hashes matched. Byte-identical typed copies and typed/HASHES.json were saved before opening original declarations. No compilation repair was necessary. All ten compile-fixes records report unchanged meaning.

Done: RESULTS.md contains the verdict table, receipts, per-claim comparisons, hostile checks of every “Does NOT say” qualification, replacement English sentences, and exposed ambiguities. Original signatures and source hashes, frozen statement/proof hashes, initial failed construction attempts, and deterministic gate receipts are saved.

Done: run_gate_blind.py uses the authorized gate helper copied byte-for-byte. Its path/glob/import changes are recorded in run_gate_blind.diff; banned-token and axiom checks are unchanged. regate.py rechecks every saved Claim and Witness, writes only JSON receipts apart from the gate's ephemeral check files, and returns nonzero on any failed check. Independent claims run in four worker threads; each proof still goes through the same deterministic gate separately.

Verification: the first full re-gate passed all 20 checks. The second re-gate started with zero previous receipts, no gate temporary directory, and no Python bytecode cache; it regenerated 20 PASS receipts and exited 0. All protected saved files retained their hashes, and temporary Lean files were removed. Details: CLEAN-REGATE-BEFORE.json and CLEAN-REGATE-VERIFIED.json. The recorded original source files retain their source hashes.

Not done: none of the requested Phase B work remains unfinished. No UNDECIDED claims or outstanding proof failures remain.

Could not do: no requested action was blocked. This check and its abstract nonempty witnesses do not establish real extraction completeness, identity authenticity, storage correctness, or protocol publication refinement; those are expressly outside the conclusions and remain premises.

Time: first saved compilation receipt 2026-10-13T04:10:49.158156+00:00; completed 2026-10-13T04:24:26.835350+00:00. Elapsed since that first receipt: 13.6 minutes. Exact session-start time was not recorded.

Scope: writes stayed under docs/lean-english/one-to-one/blind-g0n1/. No ControlStack source edits, git commands, external comparison records, sub-agents, or downloads were used.
